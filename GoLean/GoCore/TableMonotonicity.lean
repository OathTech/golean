import GoLean.GoCore.Prefix
import GoLean.GoCore.StateEqb

/-!
# Table monotonicity — a step under a SLICE of the tables is the step under the WHOLE (raft-proofs G16)

[AGENT lane core/g16-table-monotonicity-1023], 2026-10-23, on the [USER] ruling of 2026-10-23
(backlog row 48: go ahead with G16, urgent; the ask is
`~/projects/raft-proofs/docs/2026-10-23_golean-ask-table-monotonicity.md`). Re-based on the
PER-KEY relation by [AGENT lane core/g16-raise-mark-1023], 2026-10-23, on the [USER] ruling of the
same day (backlog row 48, option 1: the raise's rendering mark moved to the abort phase, so that a
relation the customer's slices satisfy AS THEY ARE could be proved).

The customer proves each raft function against a slice of the pinned wire — the function's
static call closure — and transfers the slice theorems to the whole program with ONE lemma:
a successful `stepFn` step under a context agrees with the step under any context that has the
SAME `typeDefs`, `globals` and `typeDisplays` (derived from `typeDefs`) and whose `funcs`,
`methods`, `methodSets` and `promotions` CONTAIN the slice's rows (`ProgramCtx.SubTables`,
below), lifted to `Prefix` (`prefix_mono`).

## Why a FILTER (`List.Sublist`), and what the whole program must satisfy

Every table read the machine makes is a FIRST-MATCH lookup by key (`findFunctionIn?`,
`methodInfoByFuncId?`, `methodDecl?`, `promotion?`, `methodSetCoverage?` — each `IS` a
`List.find?`, the `_eq_find?` equations), never by position; so a slice that keeps a found row
gives the same answer only if no row BEFORE it in the whole table carries the same key. Set
inclusion would not say that; a sublist (order kept) plus KEY UNIQUENESS in the whole table does
(`TablesKeyed`): the whole's first match for a key is its only row with that key, hence the kept
row. The native decoder enforces every uniqueness the proof relies on (`NativeToIR.lean`:
duplicate function ids, duplicate method-set keys and duplicate promotion keys refuse at the
wire boundary; the admission profile `Admission.lean` re-checks function keys on its own
entry), and the two Go-level facts (a member is declared on `T` or on `*T`, never both; a
promotion record never names a member the carrier declares) are what `go/types` guarantees and
`validatePromotion` re-checks; every concrete receiver is a method CARRIER (`methodReceiverAgrees`)
— but THIS module proves nothing about the decoder: the facts are PREMISES of the relation, and a
consumer discharges them once per wire. They are decidable in principle, but NO `Decidable`
instance or `Bool` checker ships (`by decide` cannot synthesize one; review fix round F5,
2026-10-23): a consumer discharges the explicit clauses by evaluation on its concrete tables
(`simp`/`rfl` over the unfolded lists) or through its reflective evaluator; a `Bool` checker over
the four tables with its soundness lemma (about a hundred lines beside `TablesKeyed`/`SliceClosed`)
is a follow-up if a consumer asks.

## Why the PER-KEY closure (and nothing else)

A successful step makes positive lookups only where a negative answer is a REFUSAL — dispatch
through `dynamicMethodSetRecorded`, a missing callee, a missing dispatch target — EXCEPT where the
machine answers from a method-set RECORD: with the carrier's record present, «no such method» is a
definite answer (the D2 wire contract: the record certifies that the carrier's whole method set is
on the wire). Three readers answer that way: the preprint phase's DECISION of a raised payload's
rewrite mark (`phaseMark` — the record first, then `Error`, then `String`; since 2026-10-23,
when the raise stopped deciding it), interface SATISFACTION for a type assertion / comma-ok / type
switch (`firstUnsatisfiedMethod?`: a «missing method N» answer is given only under the record), and
the pointer method set's emptiness in a type-assertion text (`typePkgForMessage`: `""` only under a
`full` record). So the slice must honour exactly what its records certify (`SliceClosed`):

* for every record the slice KEEPS, every method of the whole on that carrier (`T` or `*T`
  receivers — one carrier key, `methodCarrierKey?`) is kept with its `Func`, and every promotion
  record of the whole on that carrier is kept with its target's `Func` (`recordMethods`,
  `recordPromotions`) — the rule `extract_wire.py` already applies: a record is kept whole per key
  or dropped, and kept only when the carrier's methods and promotions are all selected;
* a kept `Func` keeps its `MethodInfo` (`methodOfFunc`): `dynamicDispatch?` treats a `Func` with
  no `MethodInfo` as a plain function (a decoded wire carries the two as one `program.methods[i]`
  entry, so a slice decoded from the wire has this for free).

A slice without the record REFUSES where the whole answers, which the theorem does not claim.
Nothing is required of the slice beyond its own records: no `Error`/`String` closure, no
interface-requirement closure, no per-receiver witness (the three closures of the first cut, which
grew the customer's `Inflights` slice from 12 to ~375 of 1,005 callables, measured on the twin wire;
under this relation their slices satisfy the premises unchanged — 12 and 8 callables with 6
records each).

What is NOT claimed: refusals and stops (a slice refuses where the whole dispatches; the
`.ok` premise is the whole statement), and the pool (`Multi.lean`): the sequential `stepFn`
and its `Prefix` only.
-/

namespace GoLean.GoCore

open GoLean GoLean.GoCore.Machine GoLean.GoCore.ExecutionStatement

/-! ## §1 The relation -/

/-- The context with the four sliced tables emptied: what a table-free helper sees. Two
contexts with the same `tablesFree` agree on every helper that reads only `types`,
`globals` and `typeDisplays` (§3). -/
def ProgramCtx.tablesFree (c : ProgramCtx) : ProgramCtx :=
  ⟨{ typeDefs := c.types, funcs := #[], methods := #[], globals := c.globals,
     methodSets := #[], typeDisplays := c.typeDisplays, promotions := #[] }⟩

@[simp] theorem ProgramCtx.tablesFree_types (c : ProgramCtx) : c.tablesFree.types = c.types := rfl
@[simp] theorem ProgramCtx.tablesFree_globals (c : ProgramCtx) :
    c.tablesFree.globals = c.globals := rfl
@[simp] theorem ProgramCtx.tablesFree_typeDisplays (c : ProgramCtx) :
    c.tablesFree.typeDisplays = c.typeDisplays := rfl

/-- The whole program's KEY DISCIPLINE: what makes each first-match lookup's answer the
unique row of its key, and keeps `resolveMethod?`'s arms disjoint. Every clause is a fact about
the whole program alone (decidable in principle; no instance shipped — module header). On a decoded wire they hold: the decoder refuses duplicate
function ids (hence duplicate method func-ids and, through `methodReceiverAgrees`, duplicate
(receiver, member) declarations), duplicate method-set keys, duplicate promotion keys, an empty
promotion path, a record naming a member its carrier declares (`NativeToIR.lean`,
`validatePromotion`) and a method whose receiver is not a carrier (`methodReceiverAgrees`: `T`,
`*T`, an interface, or a sync primitive); a member declared on both `T` and `*T` is rejected by
`go/types` before a wire exists; and no frontend `Func` carries a method-expression id it does not
own. This module proves none of that — the clauses are PREMISES, discharged once per wire by its
consumer. -/
structure ProgramCtx.TablesKeyed (b : ProgramCtx) : Prop where
  /-- Function ids are unique (`findFunctionIn?`; the decoder's duplicate-id refusal). -/
  funcIds : (b.functions.toList.map (·.id)).Nodup
  /-- A `Func` has at most one `MethodInfo` (`methodInfoByFuncId?`). -/
  methodFuncIds : (b.methods.toList.map (·.funcId)).Nodup
  /-- Every concrete method is the first match of its own (receiver, member) key
  (`methodDecl?`): no earlier row declares the same member on the same receiver. -/
  declFirst : ∀ m ∈ b.methods.toList, ∀ r, methodRecvDynamicTy? m = some r →
    methodDecl? b r m.id = some m
  /-- Go: a member declared on `T` is not also declared on `*T` (spec#Method_declarations,
  «the method name must be unique in the method set of the base type»). -/
  noPtrTwin : ∀ m ∈ b.methods.toList, ∀ r, methodRecvDynamicTy? m = some r →
    methodDecl? b (.pointer r) m.id = none
  /-- Every concrete receiver is a method CARRIER — `T` or `*T` for a defined `T`, or a sync
  primitive (`methodReceiverAgrees`): so a record's key names every method of its carrier, and a
  non-carrier dynamic type (`string`, `[]int`, `**T`, …) has no method anywhere. -/
  recvCarrier : ∀ m ∈ b.methods.toList, ∀ r, methodRecvDynamicTy? m = some r →
    (methodCarrierKey? b r).isSome
  /-- Method-set records are unique per carrier key (`methodSetCoverage?`; the decoder's
  duplicate-key refusal). -/
  methodSetKeys : (b.methodSets.toList.map (·.key)).Nodup
  /-- A promotion walks at least one embedded hop (the decoder refuses an empty path). Without it
  a stub record with an empty path could resolve where `nilValueMethodText?` reads the path:
  the slice would then draw the `nilValueMethodText` pick at a different width than the whole. -/
  promotionPath : ∀ p ∈ b.promotions.toList, p.path.isEmpty = false
  /-- Promotion records are unique per (carrier, member) (`promotion?`). -/
  promotionKeys : (b.promotions.toList.map fun p => (p.type, p.member)).Nodup
  /-- Promotion records are unique per method-expression id (`callee?`; the decoder's
  duplicate-promotion refusal is on this key). -/
  promotionIds : (b.promotions.toList.map fun p => methodFuncId p.type.key p.member).Nodup
  /-- No declared `Func` carries a promotion's method-expression id (`callee?` answers the
  `Func` first; a slice that dropped it would answer the record). -/
  promotionNoFunc : ∀ p ∈ b.promotions.toList,
    findFunctionIn? b.functions (methodFuncId p.type.key p.member) = none
  /-- A carrier does not both declare and promote one member (`validatePromotion`), on the
  value and the pointer box: `resolveMethod?`'s declared arms are `none` wherever its
  promoted arm answers. -/
  promotionNoDecl : ∀ p ∈ b.promotions.toList, ∀ idx, b.types.nameOf? idx = some p.type →
    methodDecl? b (.defined idx) p.member = none ∧
      methodDecl? b (.pointer (.defined idx)) p.member = none

/-- The slice's CLOSURE under the whole — PER KEY: what its own method-set records certify
(module header). Each clause is a fact about the pair (decidable in principle; no instance
shipped — module header). -/
structure ProgramCtx.SliceClosed (a b : ProgramCtx) : Prop where
  /-- A kept `Func` keeps its `MethodInfo` (`dynamicDispatch?` dispatches a method and runs a
  plain function by this table alone). -/
  methodOfFunc : ∀ m ∈ b.methods.toList, (∃ f ∈ a.functions.toList, f.id = m.funcId) →
    m ∈ a.methods.toList
  /-- A kept record's carrier keeps every method the whole declares on it (`T` and `*T`
  receivers share the carrier key), each with its `Func` (its signature is compared). -/
  recordMethods : ∀ r ∈ a.methodSets.toList, ∀ m ∈ b.methods.toList, ∀ t,
    methodRecvDynamicTy? m = some t → methodCarrierKey? b t = some r.key →
    m ∈ a.methods.toList ∧ ∀ f ∈ b.functions.toList, f.id = m.funcId → f ∈ a.functions.toList
  /-- A kept record's carrier keeps every promotion record the whole states for it, each with
  its target's `Func`. -/
  recordPromotions : ∀ r ∈ a.methodSets.toList, ∀ p ∈ b.promotions.toList, p.type.key = r.key →
    p ∈ a.promotions.toList ∧
      ∀ f, p.target = .method f → ∀ g ∈ b.functions.toList, g.id = f → g ∈ a.functions.toList

/-- **The sub-table relation** (G16): `a` is a slice of `b` — the same type table, globals and
displays; `funcs`, `methods`, `methodSets` and `promotions` sublists (filters: order kept) of
`b`'s; `b` key-disciplined; `a` closed under `b` per record. -/
structure ProgramCtx.SubTables (a b : ProgramCtx) : Prop where
  types : a.types = b.types
  globals : a.globals = b.globals
  typeDisplays : a.typeDisplays = b.typeDisplays
  functions : a.functions.toList.Sublist b.functions.toList
  methods : a.methods.toList.Sublist b.methods.toList
  methodSets : a.methodSets.toList.Sublist b.methodSets.toList
  promotions : a.promotions.toList.Sublist b.promotions.toList
  keyed : b.TablesKeyed
  closed : a.SliceClosed b

namespace ProgramCtx.SubTables

variable {a b : ProgramCtx}

theorem tablesFree_eq (h : a.SubTables b) : a.tablesFree = b.tablesFree := by
  simp only [ProgramCtx.tablesFree, h.types, h.globals, h.typeDisplays]

theorem mem_functions (h : a.SubTables b) {f : Func} (hf : f ∈ a.functions.toList) :
    f ∈ b.functions.toList := h.functions.subset hf
theorem mem_methods (h : a.SubTables b) {m : MethodInfo} (hm : m ∈ a.methods.toList) :
    m ∈ b.methods.toList := h.methods.subset hm
theorem mem_methodSets (h : a.SubTables b) {r : MethodSetRecord} (hr : r ∈ a.methodSets.toList) :
    r ∈ b.methodSets.toList := h.methodSets.subset hr
theorem mem_promotions (h : a.SubTables b) {p : Promotion} (hp : p ∈ a.promotions.toList) :
    p ∈ b.promotions.toList := h.promotions.subset hp

end ProgramCtx.SubTables

/-! ## §2 The lookups: found under the slice ⇒ found with the same value under the whole -/

namespace TableMono

/-- Two rows of a key-unique list with the same key are the same row. -/
theorem nodup_map_inj {α β : Type} {l : List α} {f : α → β} (h : (l.map f).Nodup)
    {x y : α} (hx : x ∈ l) (hy : y ∈ l) (hf : f x = f y) : x = y := by
  induction l with
  | nil => cases hx
  | cons z zs ih =>
    rw [List.map_cons, List.nodup_cons] at h
    rcases List.mem_cons.mp hx with rfl | hx' <;> rcases List.mem_cons.mp hy with rfl | hy'
    · rfl
    · exact absurd (hf ▸ List.mem_map_of_mem hy') h.1
    · exact absurd (hf ▸ List.mem_map_of_mem hx') h.1
    · exact ih h.2 hx' hy'

/-- The first match of a sublist is the first match of the list when it is the list's ONLY
matching row. -/
theorem find?_sublist_mono {α : Type} {l₁ l₂ : List α} (hs : l₁.Sublist l₂) {p : α → Bool}
    {x : α} (h : l₁.find? p = some x) (huniq : ∀ y ∈ l₂, p y = true → y = x) :
    l₂.find? p = some x := by
  have hx : x ∈ l₂ := hs.subset (List.mem_of_find?_eq_some h)
  have hpx : p x = true := List.find?_some h
  cases hl : l₂.find? p with
  | none => exact absurd hpx (by simpa using (List.find?_eq_none.mp hl x hx))
  | some y =>
    rw [huniq y (List.mem_of_find?_eq_some hl) (List.find?_some hl)]

theorem MemberId.beq_sound {x y : Declaration.MemberId} (h : (x == y) = true) : x = y := by
  cases x; cases y
  have h' : (_ && _) = true := h
  simp only [Bool.and_eq_true, beq_iff_eq] at h'
  obtain ⟨rfl, rfl⟩ := h'
  rfl

end TableMono

open TableMono

/-- `methodInfoByFuncId?` IS the first-match search of the method table by `funcId`. -/
private theorem methodInfoByFuncId?_foldl_aux (id : FuncId) :
    ∀ (l : List MethodInfo) (acc : Option MethodInfo),
      l.foldl (fun found method =>
          match found with
          | some method => some method
          | none => if method.funcId == id then some method else none) acc
        = (match acc with
           | some m => some m
           | none => l.find? (fun method => method.funcId == id))
  | [], acc => by cases acc <;> rfl
  | m :: ms, acc => by
      cases acc with
      | some g => exact methodInfoByFuncId?_foldl_aux id ms (some g)
      | none =>
          rw [List.foldl_cons, List.find?_cons]
          cases hm : (m.funcId == id)
          · simp only [Bool.false_eq_true, ↓reduceIte]
            exact methodInfoByFuncId?_foldl_aux id ms none
          · simp only [↓reduceIte]
            exact methodInfoByFuncId?_foldl_aux id ms (some m)

theorem methodInfoByFuncId?_eq_find? (ctx : ProgramCtx) (id : FuncId) :
    methodInfoByFuncId? ctx id = ctx.methods.toList.find? (fun method => method.funcId == id) := by
  unfold methodInfoByFuncId?
  rw [← Array.foldl_toList]
  exact methodInfoByFuncId?_foldl_aux id ctx.methods.toList none

theorem methodInfoByFuncId?_some {ctx : ProgramCtx} {id : FuncId} {m : MethodInfo}
    (h : methodInfoByFuncId? ctx id = some m) : m.funcId = id ∧ m ∈ ctx.methods.toList := by
  rw [methodInfoByFuncId?_eq_find?] at h
  have hp := List.find?_some h
  exact ⟨FuncId.beq_sound hp, List.mem_of_find?_eq_some h⟩

/-- `methodSetCoverage?` IS the first-match search of the record table by key. -/
private theorem methodSetCoverage?_foldl_aux (key : String) :
    ∀ (l : List MethodSetRecord) (acc : Option MethodSetCoverage),
      l.foldl (fun found record =>
          match found with
          | some _ => found
          | none => if record.key == key then some record.coverage else none) acc
        = (match acc with
           | some c => some c
           | none => (l.find? (fun record => record.key == key)).map (·.coverage))
  | [], acc => by cases acc <;> rfl
  | r :: rs, acc => by
      cases acc with
      | some g => exact methodSetCoverage?_foldl_aux key rs (some g)
      | none =>
          rw [List.foldl_cons, List.find?_cons]
          cases hr : (r.key == key)
          · simp only [Bool.false_eq_true, ↓reduceIte]
            exact methodSetCoverage?_foldl_aux key rs none
          · simp only [↓reduceIte, Option.map_some]
            exact methodSetCoverage?_foldl_aux key rs (some r.coverage)

theorem methodSetCoverage?_eq_find? (ctx : ProgramCtx) (key : String) :
    methodSetCoverage? ctx key =
      (ctx.methodSets.toList.find? (fun record => record.key == key)).map (·.coverage) := by
  unfold methodSetCoverage?
  rw [← Array.foldl_toList]
  exact methodSetCoverage?_foldl_aux key ctx.methodSets.toList none

namespace ProgramCtx.SubTables

variable {a b : ProgramCtx}

theorem findFunctionIn?_mono (h : a.SubTables b) {fid : FuncId} {f : Func}
    (hf : findFunctionIn? a.functions fid = some f) : findFunctionIn? b.functions fid = some f := by
  have hfb : f ∈ b.functions.toList := h.mem_functions (by simpa using (findFunctionIn?_some hf).2)
  have hid : f.id = fid := FuncId.beq_sound (findFunctionIn?_some hf).1
  rw [findFunctionIn?_eq_find?] at hf ⊢
  refine find?_sublist_mono h.functions hf fun y hy hpy => ?_
  exact nodup_map_inj h.keyed.funcIds hy hfb ((FuncId.beq_sound hpy).trans hid.symm)

theorem methodInfoByFuncId?_mono (h : a.SubTables b) {fid : FuncId} {m : MethodInfo}
    (hm : methodInfoByFuncId? a fid = some m) : methodInfoByFuncId? b fid = some m := by
  obtain ⟨hid, hma⟩ := methodInfoByFuncId?_some hm
  have hmb : m ∈ b.methods.toList := h.mem_methods hma
  rw [methodInfoByFuncId?_eq_find?] at hm ⊢
  refine find?_sublist_mono h.methods hm fun y hy hpy => ?_
  exact nodup_map_inj h.keyed.methodFuncIds hy hmb ((FuncId.beq_sound hpy).trans hid.symm)

/-- The row a declaration lookup finds: its member IS the key, its receiver IS the dynamic
type. -/
theorem methodDecl?_some' {ctx : ProgramCtx} {t : Ty} {M : Declaration.MemberId} {m : MethodInfo}
    (hm : methodDecl? ctx t M = some m) :
    m.id = M ∧ methodRecvDynamicTy? m = some t ∧ m ∈ ctx.methods.toList := by
  obtain ⟨h1, h2, h3⟩ := methodDecl?_some hm
  refine ⟨MemberId.beq_sound h1, ?_, by simpa using h3⟩
  cases hr : methodRecvDynamicTy? m with
  | none => rw [hr] at h2; cases h2
  | some r =>
    rw [hr, Option.some_beq_some] at h2
    rw [Ty.beq_sound h2]

theorem methodDecl?_mono (h : a.SubTables b) {t : Ty} {M : Declaration.MemberId} {m : MethodInfo}
    (hm : methodDecl? a t M = some m) : methodDecl? b t M = some m := by
  obtain ⟨rfl, hr, hma⟩ := methodDecl?_some' hm
  exact h.keyed.declFirst m (h.mem_methods hma) t hr

theorem promotion?_mono (h : a.SubTables b) {c : TypeId} {M : Declaration.MemberId} {p : Promotion}
    (hp : promotion? a c M = some p) : promotion? b c M = some p := by
  obtain ⟨hc, hM, hpa⟩ := promotion?_some hp
  have hpb : p ∈ b.promotions.toList := h.mem_promotions (by simpa using hpa)
  rw [promotion?_eq_find?] at hp ⊢
  refine find?_sublist_mono h.promotions hp fun y hy hpy => ?_
  simp only [Bool.and_eq_true, beq_iff_eq] at hpy
  refine nodup_map_inj h.keyed.promotionKeys hy hpb ?_
  rw [hpy.1, hc, MemberId.beq_sound hpy.2, MemberId.beq_sound hM]

/-- `methodSetCoverage?`: a record found under the slice is the whole's record for that key
(records are unique per key). -/
theorem methodSetCoverage?_mono (h : a.SubTables b) {key : String} {cov : MethodSetCoverage}
    (hc : methodSetCoverage? a key = some cov) : methodSetCoverage? b key = some cov := by
  rw [methodSetCoverage?_eq_find?] at hc ⊢
  cases hf : a.methodSets.toList.find? (fun record => record.key == key) with
  | none => rw [hf] at hc; cases hc
  | some r =>
    rw [hf] at hc
    have hrb : r ∈ b.methodSets.toList := h.mem_methodSets (List.mem_of_find?_eq_some hf)
    have hrk : r.key = key := by simpa using List.find?_some hf
    rw [find?_sublist_mono h.methodSets hf fun y hy hpy =>
      nodup_map_inj h.keyed.methodSetKeys hy hrb ((show y.key = key by simpa using hpy).trans hrk.symm)]
    exact hc

/-- The record a kept key names, in the slice. -/
theorem record_of_coverage {c : ProgramCtx} {key : String} {cov : MethodSetCoverage}
    (hc : methodSetCoverage? c key = some cov) : ∃ r ∈ c.methodSets.toList, r.key = key := by
  rw [methodSetCoverage?_eq_find?] at hc
  cases hf : c.methodSets.toList.find? (fun record => record.key == key) with
  | none => rw [hf] at hc; cases hc
  | some r => exact ⟨r, List.mem_of_find?_eq_some hf, by simpa using List.find?_some hf⟩

end ProgramCtx.SubTables

/-! ## §3 The table-free helpers: equal on two contexts with the same `tablesFree`

Every helper `stepFn` reaches that reads only `types`, `globals` and `typeDisplays` (82 of the
123 context-reading helpers in its call closure, enumerated 2026-10-23 by the lane's scan of
`Ops.lean`/`Machine.lean`/`StepFn.lean`), in callee-first order. Three proof shapes: `rfl`
against `tablesFree` (a non-recursive wrapper whose body is definitionally the same under the
emptied tables), `delta` + `simp` with the callees' equations, and the function's own
induction principle (`fun_induction`; the two mutual blocks `goTypeNameForMessage` and
`valueHashability`/`valueEq` by their generated principles). Every lemma is stated as
`@f a = @f b` (the `@` keeps Lean from eta-expanding a helper with an optional argument into
a lambda `simp` cannot rewrite with).

The `append` spill arm (the default-capacity pick, lane `core/g18-append-capacity-1023` beside
this one) lives in `applyStmtOp.plan`: its one lemma here is `applyStmtOp_plan_eq`, a `delta` +
`simp` over the callees' equations, so a change to that arm costs one local rework — a new
table-free callee gets its own `_eq` lemma and a place in the sweep's rewrite set. -/

namespace TableMono

set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false

variable {a b : ProgramCtx}

theorem types_eq (h : a.tablesFree = b.tablesFree) : a.types = b.types := by
  have := congrArg ProgramCtx.types h; simpa using this
theorem typeDisplays_eq (h : a.tablesFree = b.tablesFree) : a.typeDisplays = b.typeDisplays := by
  have := congrArg ProgramCtx.typeDisplays h; simpa using this
theorem globals_eq (h : a.tablesFree = b.tablesFree) : a.globals = b.globals := by
  have := congrArg ProgramCtx.globals h; simpa using this

theorem structTagCompatible_free (c : ProgramCtx) : @structTagCompatible c = @structTagCompatible c.tablesFree := rfl
theorem structTagCompatible_eq (h : a.tablesFree = b.tablesFree) : @structTagCompatible a = @structTagCompatible b := by
  rw [structTagCompatible_free a, structTagCompatible_free b, h]

theorem loadLoc_eq_app (h : a.tablesFree = b.tablesFree) (s : Store) (l : Loc) :
    loadLoc a s l = loadLoc b s l := by
  fun_induction loadLoc a s l <;> (try simp only [types_eq h, typeDisplays_eq h, globals_eq h, structTagCompatible_eq h] at *) <;> simp +zetaDelta only [loadLoc, types_eq h, typeDisplays_eq h, globals_eq h, structTagCompatible_eq h, *]
  all_goals (try (split <;> simp_all))
theorem loadLoc_eq (h : a.tablesFree = b.tablesFree) : @loadLoc a = @loadLoc b := by
  funext s l; exact loadLoc_eq_app h s l

theorem Mem_load_eq (h : a.tablesFree = b.tablesFree) : @Mem.load a = @Mem.load b := by
  delta Mem.load; simp only [types_eq h, typeDisplays_eq h, globals_eq h, structTagCompatible_eq h, loadLoc_eq h]

theorem loadRoot_eq (h : a.tablesFree = b.tablesFree) : @loadRoot a = @loadRoot b := by
  delta loadRoot; simp only [types_eq h, typeDisplays_eq h, globals_eq h, structTagCompatible_eq h, loadLoc_eq h, Mem_load_eq h]

theorem Mem_loadBinding_eq (h : a.tablesFree = b.tablesFree) : @Mem.loadBinding a = @Mem.loadBinding b := by
  delta Mem.loadBinding; simp only [types_eq h, typeDisplays_eq h, globals_eq h, structTagCompatible_eq h, loadLoc_eq h, Mem_load_eq h, loadRoot_eq h]

theorem Mem_loadBindingFor_eq (h : a.tablesFree = b.tablesFree) : @Mem.loadBindingFor a = @Mem.loadBindingFor b := by
  delta Mem.loadBindingFor; simp only [types_eq h, typeDisplays_eq h, globals_eq h, structTagCompatible_eq h, loadLoc_eq h, Mem_load_eq h, loadRoot_eq h, Mem_loadBinding_eq h]

theorem Mem_loadElems_eq_app (h : a.tablesFree = b.tablesFree) (s : Store) (base : Loc) (start n : Nat) :
    Mem.loadElems a s base start n = Mem.loadElems b s base start n := by
  fun_induction Mem.loadElems a s base start n <;> (try simp only [types_eq h, typeDisplays_eq h, globals_eq h, structTagCompatible_eq h, loadLoc_eq h, Mem_load_eq h, loadRoot_eq h, Mem_loadBinding_eq h, Mem_loadBindingFor_eq h] at *) <;> simp +zetaDelta only [Mem.loadElems, types_eq h, typeDisplays_eq h, globals_eq h, structTagCompatible_eq h, loadLoc_eq h, Mem_load_eq h, loadRoot_eq h, Mem_loadBinding_eq h, Mem_loadBindingFor_eq h, *]
  all_goals (try (split <;> simp_all))
theorem Mem_loadElems_eq (h : a.tablesFree = b.tablesFree) : @Mem.loadElems a = @Mem.loadElems b := by
  funext s base start n; exact Mem_loadElems_eq_app h s base start n

theorem Mem_loadFor_eq (h : a.tablesFree = b.tablesFree) : @Mem.loadFor a = @Mem.loadFor b := by
  delta Mem.loadFor; simp only [types_eq h, typeDisplays_eq h, globals_eq h, structTagCompatible_eq h, loadLoc_eq h, Mem_load_eq h, loadRoot_eq h, Mem_loadBinding_eq h, Mem_loadBindingFor_eq h, Mem_loadElems_eq h]

theorem Mem_loadRun_eq (h : a.tablesFree = b.tablesFree) : @Mem.loadRun a = @Mem.loadRun b := by
  delta Mem.loadRun; simp only [types_eq h, typeDisplays_eq h, globals_eq h, structTagCompatible_eq h, loadLoc_eq h, Mem_load_eq h, loadRoot_eq h, Mem_loadBinding_eq h, Mem_loadBindingFor_eq h, Mem_loadElems_eq h, Mem_loadFor_eq h]

theorem Mem_loadSlice_eq (h : a.tablesFree = b.tablesFree) : @Mem.loadSlice a = @Mem.loadSlice b := by
  delta Mem.loadSlice; simp only [types_eq h, typeDisplays_eq h, globals_eq h, structTagCompatible_eq h, loadLoc_eq h, Mem_load_eq h, loadRoot_eq h, Mem_loadBinding_eq h, Mem_loadBindingFor_eq h, Mem_loadElems_eq h, Mem_loadFor_eq h, Mem_loadRun_eq h]

theorem writeAt_eq_app (h : a.tablesFree = b.tablesFree) (n : Nat) (ty : Ty) (v : GoValue) (path : List PathStep) (w : GoValue) :
    writeAt a n ty v path w = writeAt b n ty v path w := by
  fun_induction writeAt a n ty v path w <;> (try simp only [types_eq h, typeDisplays_eq h, globals_eq h, structTagCompatible_eq h, loadLoc_eq h, Mem_load_eq h, loadRoot_eq h, Mem_loadBinding_eq h, Mem_loadBindingFor_eq h, Mem_loadElems_eq h, Mem_loadFor_eq h, Mem_loadRun_eq h, Mem_loadSlice_eq h] at *) <;> simp +zetaDelta only [writeAt, types_eq h, typeDisplays_eq h, globals_eq h, structTagCompatible_eq h, loadLoc_eq h, Mem_load_eq h, loadRoot_eq h, Mem_loadBinding_eq h, Mem_loadBindingFor_eq h, Mem_loadElems_eq h, Mem_loadFor_eq h, Mem_loadRun_eq h, Mem_loadSlice_eq h, *]
  all_goals (try (split <;> simp_all))
theorem writeAt_eq (h : a.tablesFree = b.tablesFree) : @writeAt a = @writeAt b := by
  funext n ty v path w; exact writeAt_eq_app h n ty v path w

theorem storeLoc_eq (h : a.tablesFree = b.tablesFree) : @storeLoc a = @storeLoc b := by
  delta storeLoc; simp only [types_eq h, typeDisplays_eq h, globals_eq h, structTagCompatible_eq h, loadLoc_eq h, Mem_load_eq h, loadRoot_eq h, Mem_loadBinding_eq h, Mem_loadBindingFor_eq h, Mem_loadElems_eq h, Mem_loadFor_eq h, Mem_loadRun_eq h, Mem_loadSlice_eq h, writeAt_eq h]

theorem Mem_store_eq (h : a.tablesFree = b.tablesFree) : @Mem.store a = @Mem.store b := by
  delta Mem.store; simp only [types_eq h, typeDisplays_eq h, globals_eq h, structTagCompatible_eq h, loadLoc_eq h, Mem_load_eq h, loadRoot_eq h, Mem_loadBinding_eq h, Mem_loadBindingFor_eq h, Mem_loadElems_eq h, Mem_loadFor_eq h, Mem_loadRun_eq h, Mem_loadSlice_eq h, writeAt_eq h, storeLoc_eq h]

theorem Mem_storeElems_eq_app (h : a.tablesFree = b.tablesFree) (s : Store) (base : Loc) (start : Nat) (vs : List GoValue) :
    Mem.storeElems a s base start vs = Mem.storeElems b s base start vs := by
  fun_induction Mem.storeElems a s base start vs <;> (try simp only [types_eq h, typeDisplays_eq h, globals_eq h, structTagCompatible_eq h, loadLoc_eq h, Mem_load_eq h, loadRoot_eq h, Mem_loadBinding_eq h, Mem_loadBindingFor_eq h, Mem_loadElems_eq h, Mem_loadFor_eq h, Mem_loadRun_eq h, Mem_loadSlice_eq h, writeAt_eq h, storeLoc_eq h, Mem_store_eq h] at *) <;> simp +zetaDelta only [Mem.storeElems, types_eq h, typeDisplays_eq h, globals_eq h, structTagCompatible_eq h, loadLoc_eq h, Mem_load_eq h, loadRoot_eq h, Mem_loadBinding_eq h, Mem_loadBindingFor_eq h, Mem_loadElems_eq h, Mem_loadFor_eq h, Mem_loadRun_eq h, Mem_loadSlice_eq h, writeAt_eq h, storeLoc_eq h, Mem_store_eq h, *]
  all_goals (try (split <;> simp_all))
theorem Mem_storeElems_eq (h : a.tablesFree = b.tablesFree) : @Mem.storeElems a = @Mem.storeElems b := by
  funext s base start vs; exact Mem_storeElems_eq_app h s base start vs

theorem Mem_storeRun_eq (h : a.tablesFree = b.tablesFree) : @Mem.storeRun a = @Mem.storeRun b := by
  delta Mem.storeRun; simp only [types_eq h, typeDisplays_eq h, globals_eq h, structTagCompatible_eq h, loadLoc_eq h, Mem_load_eq h, loadRoot_eq h, Mem_loadBinding_eq h, Mem_loadBindingFor_eq h, Mem_loadElems_eq h, Mem_loadFor_eq h, Mem_loadRun_eq h, Mem_loadSlice_eq h, writeAt_eq h, storeLoc_eq h, Mem_store_eq h, Mem_storeElems_eq h]

theorem normalizeValueForTy_free (c : ProgramCtx) : @normalizeValueForTy c = @normalizeValueForTy c.tablesFree := rfl
theorem normalizeValueForTy_eq (h : a.tablesFree = b.tablesFree) : @normalizeValueForTy a = @normalizeValueForTy b := by
  rw [normalizeValueForTy_free a, normalizeValueForTy_free b, h]

theorem Store_alloc_free (c : ProgramCtx) : @Store.alloc c = @Store.alloc c.tablesFree := rfl
theorem Store_alloc_eq (h : a.tablesFree = b.tablesFree) : @Store.alloc a = @Store.alloc b := by
  rw [Store_alloc_free a, Store_alloc_free b, h]

theorem typeDisplay?_free (c : ProgramCtx) : @typeDisplay? c = @typeDisplay? c.tablesFree := rfl
theorem typeDisplay?_eq (h : a.tablesFree = b.tablesFree) : @typeDisplay? a = @typeDisplay? b := by
  rw [typeDisplay?_free a, typeDisplay?_free b, h]

theorem displayNameOfId_free (c : ProgramCtx) : @displayNameOfId c = @displayNameOfId c.tablesFree := rfl
theorem displayNameOfId_eq (h : a.tablesFree = b.tablesFree) : @displayNameOfId a = @displayNameOfId b := by
  rw [displayNameOfId_free a, displayNameOfId_free b, h]

theorem displayNameOf_free (c : ProgramCtx) : @displayNameOf c = @displayNameOf c.tablesFree := rfl
theorem displayNameOf_eq (h : a.tablesFree = b.tablesFree) : @displayNameOf a = @displayNameOf b := by
  rw [displayNameOf_free a, displayNameOf_free b, h]

theorem goTypeNameForMessage_eq_app (h : a.tablesFree = b.tablesFree) (t : Ty) :
    goTypeNameForMessage a t = goTypeNameForMessage b t := by
  refine goTypeNameForMessage.induct a (motive_1 := fun t => goTypeNameForMessage a t = goTypeNameForMessage b t)
    (motive_2 := fun l => goTypeNamesForMessage a l = goTypeNamesForMessage b l)
    (motive_3 := fun l => goTypeNamesForMessageVariadic a l = goTypeNamesForMessageVariadic b l)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ t
  all_goals intros
  all_goals (try (simp only [goTypeNameForMessage, goTypeNamesForMessage, goTypeNamesForMessageVariadic,
    displayNameOf_eq h, displayNameOfId_eq h, *]; done))
theorem goTypeNameForMessage_eq (h : a.tablesFree = b.tablesFree) :
    @goTypeNameForMessage a = @goTypeNameForMessage b := funext (goTypeNameForMessage_eq_app h)

theorem payloadDynamicTypeNote_eq (h : a.tablesFree = b.tablesFree) : @payloadDynamicTypeNote a = @payloadDynamicTypeNote b := by
  delta payloadDynamicTypeNote; simp only [types_eq h, typeDisplays_eq h, globals_eq h, structTagCompatible_eq h, loadLoc_eq h, Mem_load_eq h, loadRoot_eq h, Mem_loadBinding_eq h, Mem_loadBindingFor_eq h, Mem_loadElems_eq h, Mem_loadFor_eq h, Mem_loadRun_eq h, Mem_loadSlice_eq h, writeAt_eq h, storeLoc_eq h, Mem_store_eq h, Mem_storeElems_eq h, Mem_storeRun_eq h, normalizeValueForTy_eq h, Store_alloc_eq h, typeDisplay?_eq h, displayNameOfId_eq h, displayNameOf_eq h, goTypeNameForMessage_eq h]

theorem abortRefusal_eq (h : a.tablesFree = b.tablesFree) : @abortRefusal a = @abortRefusal b := by
  delta abortRefusal; simp only [types_eq h, typeDisplays_eq h, globals_eq h, structTagCompatible_eq h, loadLoc_eq h, Mem_load_eq h, loadRoot_eq h, Mem_loadBinding_eq h, Mem_loadBindingFor_eq h, Mem_loadElems_eq h, Mem_loadFor_eq h, Mem_loadRun_eq h, Mem_loadSlice_eq h, writeAt_eq h, storeLoc_eq h, Mem_store_eq h, Mem_storeElems_eq h, Mem_storeRun_eq h, normalizeValueForTy_eq h, Store_alloc_eq h, typeDisplay?_eq h, displayNameOfId_eq h, displayNameOf_eq h, goTypeNameForMessage_eq h, payloadDynamicTypeNote_eq h]

theorem methodCarrierKey?_free (c : ProgramCtx) : @methodCarrierKey? c = @methodCarrierKey? c.tablesFree := rfl
theorem methodCarrierKey?_eq (h : a.tablesFree = b.tablesFree) : @methodCarrierKey? a = @methodCarrierKey? b := by
  rw [methodCarrierKey?_free a, methodCarrierKey?_free b, h]

theorem interfaceDeclaredMethods?_free (c : ProgramCtx) : @interfaceDeclaredMethods? c = @interfaceDeclaredMethods? c.tablesFree := rfl
theorem interfaceDeclaredMethods?_eq (h : a.tablesFree = b.tablesFree) : @interfaceDeclaredMethods? a = @interfaceDeclaredMethods? b := by
  rw [interfaceDeclaredMethods?_free a, interfaceDeclaredMethods?_free b, h]

theorem defaultValue_free (c : ProgramCtx) : @defaultValue c = @defaultValue c.tablesFree := rfl
theorem defaultValue_eq (h : a.tablesFree = b.tablesFree) : @defaultValue a = @defaultValue b := by
  rw [defaultValue_free a, defaultValue_free b, h]

theorem allocDecls_eq_app (h : a.tablesFree = b.tablesFree) (env : LocalEnv) (s : Store) (l : List Param) :
    allocDecls a env s l = allocDecls b env s l := by
  fun_induction allocDecls a env s l <;> (try simp only [types_eq h, typeDisplays_eq h, globals_eq h, structTagCompatible_eq h, loadLoc_eq h, Mem_load_eq h, loadRoot_eq h, Mem_loadBinding_eq h, Mem_loadBindingFor_eq h, Mem_loadElems_eq h, Mem_loadFor_eq h, Mem_loadRun_eq h, Mem_loadSlice_eq h, writeAt_eq h, storeLoc_eq h, Mem_store_eq h, Mem_storeElems_eq h, Mem_storeRun_eq h, normalizeValueForTy_eq h, Store_alloc_eq h, typeDisplay?_eq h, displayNameOfId_eq h, displayNameOf_eq h, goTypeNameForMessage_eq h, payloadDynamicTypeNote_eq h, abortRefusal_eq h, methodCarrierKey?_eq h, interfaceDeclaredMethods?_eq h, defaultValue_eq h] at *) <;> simp +zetaDelta only [allocDecls, types_eq h, typeDisplays_eq h, globals_eq h, structTagCompatible_eq h, loadLoc_eq h, Mem_load_eq h, loadRoot_eq h, Mem_loadBinding_eq h, Mem_loadBindingFor_eq h, Mem_loadElems_eq h, Mem_loadFor_eq h, Mem_loadRun_eq h, Mem_loadSlice_eq h, writeAt_eq h, storeLoc_eq h, Mem_store_eq h, Mem_storeElems_eq h, Mem_storeRun_eq h, normalizeValueForTy_eq h, Store_alloc_eq h, typeDisplay?_eq h, displayNameOfId_eq h, displayNameOf_eq h, goTypeNameForMessage_eq h, payloadDynamicTypeNote_eq h, abortRefusal_eq h, methodCarrierKey?_eq h, interfaceDeclaredMethods?_eq h, defaultValue_eq h, *]
  all_goals (try (split <;> simp_all))
theorem allocDecls_eq (h : a.tablesFree = b.tablesFree) : @allocDecls a = @allocDecls b := by
  funext env s l; exact allocDecls_eq_app h env s l

theorem atomicStore_eq (h : a.tablesFree = b.tablesFree) : @atomicStore a = @atomicStore b := by
  delta atomicStore; simp only [types_eq h, typeDisplays_eq h, globals_eq h, structTagCompatible_eq h, loadLoc_eq h, Mem_load_eq h, loadRoot_eq h, Mem_loadBinding_eq h, Mem_loadBindingFor_eq h, Mem_loadElems_eq h, Mem_loadFor_eq h, Mem_loadRun_eq h, Mem_loadSlice_eq h, writeAt_eq h, storeLoc_eq h, Mem_store_eq h, Mem_storeElems_eq h, Mem_storeRun_eq h, normalizeValueForTy_eq h, Store_alloc_eq h, typeDisplay?_eq h, displayNameOfId_eq h, displayNameOf_eq h, goTypeNameForMessage_eq h, payloadDynamicTypeNote_eq h, abortRefusal_eq h, methodCarrierKey?_eq h, interfaceDeclaredMethods?_eq h, defaultValue_eq h, allocDecls_eq h]

theorem applyAtomicOp_eq (h : a.tablesFree = b.tablesFree) : @applyAtomicOp a = @applyAtomicOp b := by
  delta applyAtomicOp; simp only [types_eq h, typeDisplays_eq h, globals_eq h, structTagCompatible_eq h, loadLoc_eq h, Mem_load_eq h, loadRoot_eq h, Mem_loadBinding_eq h, Mem_loadBindingFor_eq h, Mem_loadElems_eq h, Mem_loadFor_eq h, Mem_loadRun_eq h, Mem_loadSlice_eq h, writeAt_eq h, storeLoc_eq h, Mem_store_eq h, Mem_storeElems_eq h, Mem_storeRun_eq h, normalizeValueForTy_eq h, Store_alloc_eq h, typeDisplay?_eq h, displayNameOfId_eq h, displayNameOf_eq h, goTypeNameForMessage_eq h, payloadDynamicTypeNote_eq h, abortRefusal_eq h, methodCarrierKey?_eq h, interfaceDeclaredMethods?_eq h, defaultValue_eq h, allocDecls_eq h, atomicStore_eq h]

theorem applyChanOp_free (c : ProgramCtx) : @applyChanOp c = @applyChanOp c.tablesFree := rfl
theorem applyChanOp_eq (h : a.tablesFree = b.tablesFree) : @applyChanOp a = @applyChanOp b := by
  rw [applyChanOp_free a, applyChanOp_free b, h]

theorem tyUncomparable_free (c : ProgramCtx) : @tyUncomparable c = @tyUncomparable c.tablesFree := rfl
theorem tyUncomparable_eq (h : a.tablesFree = b.tablesFree) : @tyUncomparable a = @tyUncomparable b := by
  rw [tyUncomparable_free a, tyUncomparable_free b, h]

theorem valueHashability_eq_app (h : a.tablesFree = b.tablesFree) (v : GoValue) :
    valueHashability a v = valueHashability b v := by
  apply valueHashability.induct a (motive_1 := fun v => valueHashability a v = valueHashability b v)
    (motive_2 := fun l => valueHashabilityList a l = valueHashabilityList b l)
    (motive_3 := fun l => valueHashabilityFields a l = valueHashabilityFields b l)
  all_goals intros
  all_goals (try simp only [tyUncomparable_eq h, goTypeNameForMessage_eq h, types_eq h, typeDisplays_eq h] at *)
  all_goals (try rw [valueHashability.eq_def (ctx := a), valueHashability.eq_def (ctx := b)])
  all_goals (try rw [valueHashabilityList.eq_def (ctx := a), valueHashabilityList.eq_def (ctx := b)])
  all_goals (try rw [valueHashabilityFields.eq_def (ctx := a), valueHashabilityFields.eq_def (ctx := b)])
  all_goals (try simp only [tyUncomparable_eq h, goTypeNameForMessage_eq h, types_eq h, typeDisplays_eq h, *])
  all_goals (try (split <;> simp_all))
theorem valueHashability_eq (h : a.tablesFree = b.tablesFree) :
    @valueHashability a = @valueHashability b := funext (valueHashability_eq_app h)

theorem checkKeyHashable_eq (h : a.tablesFree = b.tablesFree) : @checkKeyHashable a = @checkKeyHashable b := by
  delta checkKeyHashable; simp only [types_eq h, typeDisplays_eq h, globals_eq h, structTagCompatible_eq h, loadLoc_eq h, Mem_load_eq h, loadRoot_eq h, Mem_loadBinding_eq h, Mem_loadBindingFor_eq h, Mem_loadElems_eq h, Mem_loadFor_eq h, Mem_loadRun_eq h, Mem_loadSlice_eq h, writeAt_eq h, storeLoc_eq h, Mem_store_eq h, Mem_storeElems_eq h, Mem_storeRun_eq h, normalizeValueForTy_eq h, Store_alloc_eq h, typeDisplay?_eq h, displayNameOfId_eq h, displayNameOf_eq h, goTypeNameForMessage_eq h, payloadDynamicTypeNote_eq h, abortRefusal_eq h, methodCarrierKey?_eq h, interfaceDeclaredMethods?_eq h, defaultValue_eq h, allocDecls_eq h, atomicStore_eq h, applyAtomicOp_eq h, applyChanOp_eq h, tyUncomparable_eq h, valueHashability_eq h]

theorem valueEq_eq_app (h : a.tablesFree = b.tablesFree) (ty : Ty) (l r : GoValue) :
    valueEq a ty l r = valueEq b ty l r := by
  apply valueEq.induct a (motive_1 := fun ty l r => valueEq a ty l r = valueEq b ty l r)
    (motive_2 := fun fs l r => valueEqFields a fs l r = valueEqFields b fs l r)
    (motive_3 := fun ty l r => valueEqList a ty l r = valueEqList b ty l r)
  all_goals intros
  all_goals (try simp only [types_eq h, typeDisplays_eq h, globals_eq h, structTagCompatible_eq h, loadLoc_eq h, Mem_load_eq h, loadRoot_eq h, Mem_loadBinding_eq h, Mem_loadBindingFor_eq h, Mem_loadElems_eq h, Mem_loadFor_eq h, Mem_loadRun_eq h, Mem_loadSlice_eq h, writeAt_eq h, storeLoc_eq h, Mem_store_eq h, Mem_storeElems_eq h, Mem_storeRun_eq h, normalizeValueForTy_eq h, Store_alloc_eq h, typeDisplay?_eq h, displayNameOfId_eq h, displayNameOf_eq h, goTypeNameForMessage_eq h, payloadDynamicTypeNote_eq h, abortRefusal_eq h, methodCarrierKey?_eq h, interfaceDeclaredMethods?_eq h, defaultValue_eq h, allocDecls_eq h, atomicStore_eq h, applyAtomicOp_eq h, applyChanOp_eq h, tyUncomparable_eq h, valueHashability_eq h, checkKeyHashable_eq h, *] at *)
  all_goals (try rw [valueEq.eq_def (ctx := a), valueEq.eq_def (ctx := b)])
  all_goals (try rw [valueEqList.eq_def (ctx := a), valueEqList.eq_def (ctx := b)])
  all_goals (try rw [valueEqFields.eq_def (ctx := a), valueEqFields.eq_def (ctx := b)])
  all_goals (try simp +zetaDelta only [types_eq h, typeDisplays_eq h, globals_eq h, structTagCompatible_eq h, loadLoc_eq h, Mem_load_eq h, loadRoot_eq h, Mem_loadBinding_eq h, Mem_loadBindingFor_eq h, Mem_loadElems_eq h, Mem_loadFor_eq h, Mem_loadRun_eq h, Mem_loadSlice_eq h, writeAt_eq h, storeLoc_eq h, Mem_store_eq h, Mem_storeElems_eq h, Mem_storeRun_eq h, normalizeValueForTy_eq h, Store_alloc_eq h, typeDisplay?_eq h, displayNameOfId_eq h, displayNameOf_eq h, goTypeNameForMessage_eq h, payloadDynamicTypeNote_eq h, abortRefusal_eq h, methodCarrierKey?_eq h, interfaceDeclaredMethods?_eq h, defaultValue_eq h, allocDecls_eq h, atomicStore_eq h, applyAtomicOp_eq h, applyChanOp_eq h, tyUncomparable_eq h, valueHashability_eq h, checkKeyHashable_eq h, *])
  all_goals (try (split <;> simp_all))
theorem valueEq_eq (h : a.tablesFree = b.tablesFree) : @valueEq a = @valueEq b :=
  funext fun ty => funext fun l => funext fun r => valueEq_eq_app h ty l r

theorem mapEntryIndex?_eq (h : a.tablesFree = b.tablesFree) : @mapEntryIndex? a = @mapEntryIndex? b := by
  delta mapEntryIndex?; simp only [types_eq h, typeDisplays_eq h, globals_eq h, structTagCompatible_eq h, loadLoc_eq h, Mem_load_eq h, loadRoot_eq h, Mem_loadBinding_eq h, Mem_loadBindingFor_eq h, Mem_loadElems_eq h, Mem_loadFor_eq h, Mem_loadRun_eq h, Mem_loadSlice_eq h, writeAt_eq h, storeLoc_eq h, Mem_store_eq h, Mem_storeElems_eq h, Mem_storeRun_eq h, normalizeValueForTy_eq h, Store_alloc_eq h, typeDisplay?_eq h, displayNameOfId_eq h, displayNameOf_eq h, goTypeNameForMessage_eq h, payloadDynamicTypeNote_eq h, abortRefusal_eq h, methodCarrierKey?_eq h, interfaceDeclaredMethods?_eq h, defaultValue_eq h, allocDecls_eq h, atomicStore_eq h, applyAtomicOp_eq h, applyChanOp_eq h, tyUncomparable_eq h, valueHashability_eq h, checkKeyHashable_eq h, valueEq_eq h]

theorem mapLookupValue_eq (h : a.tablesFree = b.tablesFree) : @mapLookupValue a = @mapLookupValue b := by
  delta mapLookupValue; simp only [types_eq h, typeDisplays_eq h, globals_eq h, structTagCompatible_eq h, loadLoc_eq h, Mem_load_eq h, loadRoot_eq h, Mem_loadBinding_eq h, Mem_loadBindingFor_eq h, Mem_loadElems_eq h, Mem_loadFor_eq h, Mem_loadRun_eq h, Mem_loadSlice_eq h, writeAt_eq h, storeLoc_eq h, Mem_store_eq h, Mem_storeElems_eq h, Mem_storeRun_eq h, normalizeValueForTy_eq h, Store_alloc_eq h, typeDisplay?_eq h, displayNameOfId_eq h, displayNameOf_eq h, goTypeNameForMessage_eq h, payloadDynamicTypeNote_eq h, abortRefusal_eq h, methodCarrierKey?_eq h, interfaceDeclaredMethods?_eq h, defaultValue_eq h, allocDecls_eq h, atomicStore_eq h, applyAtomicOp_eq h, applyChanOp_eq h, tyUncomparable_eq h, valueHashability_eq h, checkKeyHashable_eq h, valueEq_eq h, mapEntryIndex?_eq h]

theorem commitClause_free (c : ProgramCtx) : @commitClause c = @commitClause c.tablesFree := rfl
theorem commitClause_eq (h : a.tablesFree = b.tablesFree) : @commitClause a = @commitClause b := by
  rw [commitClause_free a, commitClause_free b, h]

theorem applySelectCore_free (c : ProgramCtx) : @applySelectCore c = @applySelectCore c.tablesFree := rfl
theorem applySelectCore_eq (h : a.tablesFree = b.tablesFree) : @applySelectCore a = @applySelectCore b := by
  rw [applySelectCore_free a, applySelectCore_free b, h]

theorem applySelect_free (c : ProgramCtx) : @applySelect c = @applySelect c.tablesFree := rfl
theorem applySelect_eq (h : a.tablesFree = b.tablesFree) : @applySelect a = @applySelect b := by
  rw [applySelect_free a, applySelect_free b, h]

theorem applySlice_eq (h : a.tablesFree = b.tablesFree) : @applySlice a = @applySlice b := by
  delta applySlice; simp only [types_eq h, typeDisplays_eq h, globals_eq h, structTagCompatible_eq h, loadLoc_eq h, Mem_load_eq h, loadRoot_eq h, Mem_loadBinding_eq h, Mem_loadBindingFor_eq h, Mem_loadElems_eq h, Mem_loadFor_eq h, Mem_loadRun_eq h, Mem_loadSlice_eq h, writeAt_eq h, storeLoc_eq h, Mem_store_eq h, Mem_storeElems_eq h, Mem_storeRun_eq h, normalizeValueForTy_eq h, Store_alloc_eq h, typeDisplay?_eq h, displayNameOfId_eq h, displayNameOf_eq h, goTypeNameForMessage_eq h, payloadDynamicTypeNote_eq h, abortRefusal_eq h, methodCarrierKey?_eq h, interfaceDeclaredMethods?_eq h, defaultValue_eq h, allocDecls_eq h, atomicStore_eq h, applyAtomicOp_eq h, applyChanOp_eq h, tyUncomparable_eq h, valueHashability_eq h, checkKeyHashable_eq h, valueEq_eq h, mapEntryIndex?_eq h, mapLookupValue_eq h, commitClause_eq h, applySelectCore_eq h, applySelect_eq h]

theorem buildArrayValue_free (c : ProgramCtx) : @buildArrayValue c = @buildArrayValue c.tablesFree := rfl
theorem buildArrayValue_eq (h : a.tablesFree = b.tablesFree) : @buildArrayValue a = @buildArrayValue b := by
  rw [buildArrayValue_free a, buildArrayValue_free b, h]

theorem buildDefaultArrayValue_free (c : ProgramCtx) : @buildDefaultArrayValue c = @buildDefaultArrayValue c.tablesFree := rfl
theorem buildDefaultArrayValue_eq (h : a.tablesFree = b.tablesFree) : @buildDefaultArrayValue a = @buildDefaultArrayValue b := by
  rw [buildDefaultArrayValue_free a, buildDefaultArrayValue_free b, h]

theorem mapAssignValue_plan_eq (h : a.tablesFree = b.tablesFree) : @mapAssignValue.plan a = @mapAssignValue.plan b := by
  delta mapAssignValue.plan; simp only [types_eq h, typeDisplays_eq h, globals_eq h, structTagCompatible_eq h, loadLoc_eq h, Mem_load_eq h, loadRoot_eq h, Mem_loadBinding_eq h, Mem_loadBindingFor_eq h, Mem_loadElems_eq h, Mem_loadFor_eq h, Mem_loadRun_eq h, Mem_loadSlice_eq h, writeAt_eq h, storeLoc_eq h, Mem_store_eq h, Mem_storeElems_eq h, Mem_storeRun_eq h, normalizeValueForTy_eq h, Store_alloc_eq h, typeDisplay?_eq h, displayNameOfId_eq h, displayNameOf_eq h, goTypeNameForMessage_eq h, payloadDynamicTypeNote_eq h, abortRefusal_eq h, methodCarrierKey?_eq h, interfaceDeclaredMethods?_eq h, defaultValue_eq h, allocDecls_eq h, atomicStore_eq h, applyAtomicOp_eq h, applyChanOp_eq h, tyUncomparable_eq h, valueHashability_eq h, checkKeyHashable_eq h, valueEq_eq h, mapEntryIndex?_eq h, mapLookupValue_eq h, commitClause_eq h, applySelectCore_eq h, applySelect_eq h, applySlice_eq h, buildArrayValue_eq h, buildDefaultArrayValue_eq h]

theorem applyStmtOpCore_plan_eq (h : a.tablesFree = b.tablesFree) : @applyStmtOpCore.plan a = @applyStmtOpCore.plan b := by
  delta applyStmtOpCore.plan; simp only [types_eq h, typeDisplays_eq h, globals_eq h, structTagCompatible_eq h, loadLoc_eq h, Mem_load_eq h, loadRoot_eq h, Mem_loadBinding_eq h, Mem_loadBindingFor_eq h, Mem_loadElems_eq h, Mem_loadFor_eq h, Mem_loadRun_eq h, Mem_loadSlice_eq h, writeAt_eq h, storeLoc_eq h, Mem_store_eq h, Mem_storeElems_eq h, Mem_storeRun_eq h, normalizeValueForTy_eq h, Store_alloc_eq h, typeDisplay?_eq h, displayNameOfId_eq h, displayNameOf_eq h, goTypeNameForMessage_eq h, payloadDynamicTypeNote_eq h, abortRefusal_eq h, methodCarrierKey?_eq h, interfaceDeclaredMethods?_eq h, defaultValue_eq h, allocDecls_eq h, atomicStore_eq h, applyAtomicOp_eq h, applyChanOp_eq h, tyUncomparable_eq h, valueHashability_eq h, checkKeyHashable_eq h, valueEq_eq h, mapEntryIndex?_eq h, mapLookupValue_eq h, commitClause_eq h, applySelectCore_eq h, applySelect_eq h, applySlice_eq h, buildArrayValue_eq h, buildDefaultArrayValue_eq h, mapAssignValue_plan_eq h]

theorem buildAppendBackingValue_free (c : ProgramCtx) : @buildAppendBackingValue c = @buildAppendBackingValue c.tablesFree := rfl
theorem buildAppendBackingValue_eq (h : a.tablesFree = b.tablesFree) : @buildAppendBackingValue a = @buildAppendBackingValue b := by
  rw [buildAppendBackingValue_free a, buildAppendBackingValue_free b, h]

theorem applyStmtOp_plan_eq (h : a.tablesFree = b.tablesFree) : @applyStmtOp.plan a = @applyStmtOp.plan b := by
  delta applyStmtOp.plan; simp only [types_eq h, typeDisplays_eq h, globals_eq h, structTagCompatible_eq h, loadLoc_eq h, Mem_load_eq h, loadRoot_eq h, Mem_loadBinding_eq h, Mem_loadBindingFor_eq h, Mem_loadElems_eq h, Mem_loadFor_eq h, Mem_loadRun_eq h, Mem_loadSlice_eq h, writeAt_eq h, storeLoc_eq h, Mem_store_eq h, Mem_storeElems_eq h, Mem_storeRun_eq h, normalizeValueForTy_eq h, Store_alloc_eq h, typeDisplay?_eq h, displayNameOfId_eq h, displayNameOf_eq h, goTypeNameForMessage_eq h, payloadDynamicTypeNote_eq h, abortRefusal_eq h, methodCarrierKey?_eq h, interfaceDeclaredMethods?_eq h, defaultValue_eq h, allocDecls_eq h, atomicStore_eq h, applyAtomicOp_eq h, applyChanOp_eq h, tyUncomparable_eq h, valueHashability_eq h, checkKeyHashable_eq h, valueEq_eq h, mapEntryIndex?_eq h, mapLookupValue_eq h, commitClause_eq h, applySelectCore_eq h, applySelect_eq h, applySlice_eq h, buildArrayValue_eq h, buildDefaultArrayValue_eq h, mapAssignValue_plan_eq h, applyStmtOpCore_plan_eq h, buildAppendBackingValue_eq h]

theorem buildStructFields_eq_app (h : a.tablesFree = b.tablesFree) (fs : List FieldDef) (vs : List GoValue) :
    buildStructFields a fs vs = buildStructFields b fs vs := by
  fun_induction buildStructFields a fs vs <;> (try simp only [types_eq h, typeDisplays_eq h, globals_eq h, structTagCompatible_eq h, loadLoc_eq h, Mem_load_eq h, loadRoot_eq h, Mem_loadBinding_eq h, Mem_loadBindingFor_eq h, Mem_loadElems_eq h, Mem_loadFor_eq h, Mem_loadRun_eq h, Mem_loadSlice_eq h, writeAt_eq h, storeLoc_eq h, Mem_store_eq h, Mem_storeElems_eq h, Mem_storeRun_eq h, normalizeValueForTy_eq h, Store_alloc_eq h, typeDisplay?_eq h, displayNameOfId_eq h, displayNameOf_eq h, goTypeNameForMessage_eq h, payloadDynamicTypeNote_eq h, abortRefusal_eq h, methodCarrierKey?_eq h, interfaceDeclaredMethods?_eq h, defaultValue_eq h, allocDecls_eq h, atomicStore_eq h, applyAtomicOp_eq h, applyChanOp_eq h, tyUncomparable_eq h, valueHashability_eq h, checkKeyHashable_eq h, valueEq_eq h, mapEntryIndex?_eq h, mapLookupValue_eq h, commitClause_eq h, applySelectCore_eq h, applySelect_eq h, applySlice_eq h, buildArrayValue_eq h, buildDefaultArrayValue_eq h, mapAssignValue_plan_eq h, applyStmtOpCore_plan_eq h, buildAppendBackingValue_eq h, applyStmtOp_plan_eq h] at *) <;> simp +zetaDelta only [buildStructFields, types_eq h, typeDisplays_eq h, globals_eq h, structTagCompatible_eq h, loadLoc_eq h, Mem_load_eq h, loadRoot_eq h, Mem_loadBinding_eq h, Mem_loadBindingFor_eq h, Mem_loadElems_eq h, Mem_loadFor_eq h, Mem_loadRun_eq h, Mem_loadSlice_eq h, writeAt_eq h, storeLoc_eq h, Mem_store_eq h, Mem_storeElems_eq h, Mem_storeRun_eq h, normalizeValueForTy_eq h, Store_alloc_eq h, typeDisplay?_eq h, displayNameOfId_eq h, displayNameOf_eq h, goTypeNameForMessage_eq h, payloadDynamicTypeNote_eq h, abortRefusal_eq h, methodCarrierKey?_eq h, interfaceDeclaredMethods?_eq h, defaultValue_eq h, allocDecls_eq h, atomicStore_eq h, applyAtomicOp_eq h, applyChanOp_eq h, tyUncomparable_eq h, valueHashability_eq h, checkKeyHashable_eq h, valueEq_eq h, mapEntryIndex?_eq h, mapLookupValue_eq h, commitClause_eq h, applySelectCore_eq h, applySelect_eq h, applySlice_eq h, buildArrayValue_eq h, buildDefaultArrayValue_eq h, mapAssignValue_plan_eq h, applyStmtOpCore_plan_eq h, buildAppendBackingValue_eq h, applyStmtOp_plan_eq h, *]
  all_goals (try (split <;> simp_all))
theorem buildStructFields_eq (h : a.tablesFree = b.tablesFree) : @buildStructFields a = @buildStructFields b := by
  funext fs vs; exact buildStructFields_eq_app h fs vs

theorem buildStructValue_eq (h : a.tablesFree = b.tablesFree) : @buildStructValue a = @buildStructValue b := by
  delta buildStructValue; simp only [types_eq h, typeDisplays_eq h, globals_eq h, structTagCompatible_eq h, loadLoc_eq h, Mem_load_eq h, loadRoot_eq h, Mem_loadBinding_eq h, Mem_loadBindingFor_eq h, Mem_loadElems_eq h, Mem_loadFor_eq h, Mem_loadRun_eq h, Mem_loadSlice_eq h, writeAt_eq h, storeLoc_eq h, Mem_store_eq h, Mem_storeElems_eq h, Mem_storeRun_eq h, normalizeValueForTy_eq h, Store_alloc_eq h, typeDisplay?_eq h, displayNameOfId_eq h, displayNameOf_eq h, goTypeNameForMessage_eq h, payloadDynamicTypeNote_eq h, abortRefusal_eq h, methodCarrierKey?_eq h, interfaceDeclaredMethods?_eq h, defaultValue_eq h, allocDecls_eq h, atomicStore_eq h, applyAtomicOp_eq h, applyChanOp_eq h, tyUncomparable_eq h, valueHashability_eq h, checkKeyHashable_eq h, valueEq_eq h, mapEntryIndex?_eq h, mapLookupValue_eq h, commitClause_eq h, applySelectCore_eq h, applySelect_eq h, applySlice_eq h, buildArrayValue_eq h, buildDefaultArrayValue_eq h, mapAssignValue_plan_eq h, applyStmtOpCore_plan_eq h, buildAppendBackingValue_eq h, applyStmtOp_plan_eq h, buildStructFields_eq h]

theorem convertValueToTy_free (c : ProgramCtx) : @convertValueToTy c = @convertValueToTy c.tablesFree := rfl
theorem convertValueToTy_eq (h : a.tablesFree = b.tablesFree) : @convertValueToTy a = @convertValueToTy b := by
  rw [convertValueToTy_free a, convertValueToTy_free b, h]

theorem indexTargetLoc_eq (h : a.tablesFree = b.tablesFree) : @indexTargetLoc a = @indexTargetLoc b := by
  delta indexTargetLoc; simp only [types_eq h, typeDisplays_eq h, globals_eq h, structTagCompatible_eq h, loadLoc_eq h, Mem_load_eq h, loadRoot_eq h, Mem_loadBinding_eq h, Mem_loadBindingFor_eq h, Mem_loadElems_eq h, Mem_loadFor_eq h, Mem_loadRun_eq h, Mem_loadSlice_eq h, writeAt_eq h, storeLoc_eq h, Mem_store_eq h, Mem_storeElems_eq h, Mem_storeRun_eq h, normalizeValueForTy_eq h, Store_alloc_eq h, typeDisplay?_eq h, displayNameOfId_eq h, displayNameOf_eq h, goTypeNameForMessage_eq h, payloadDynamicTypeNote_eq h, abortRefusal_eq h, methodCarrierKey?_eq h, interfaceDeclaredMethods?_eq h, defaultValue_eq h, allocDecls_eq h, atomicStore_eq h, applyAtomicOp_eq h, applyChanOp_eq h, tyUncomparable_eq h, valueHashability_eq h, checkKeyHashable_eq h, valueEq_eq h, mapEntryIndex?_eq h, mapLookupValue_eq h, commitClause_eq h, applySelectCore_eq h, applySelect_eq h, applySlice_eq h, buildArrayValue_eq h, buildDefaultArrayValue_eq h, mapAssignValue_plan_eq h, applyStmtOpCore_plan_eq h, buildAppendBackingValue_eq h, applyStmtOp_plan_eq h, buildStructFields_eq h, buildStructValue_eq h, convertValueToTy_eq h]

theorem dynamicTypeNameForMessage_eq (h : a.tablesFree = b.tablesFree) : @dynamicTypeNameForMessage a = @dynamicTypeNameForMessage b := by
  delta dynamicTypeNameForMessage; simp only [types_eq h, typeDisplays_eq h, globals_eq h, structTagCompatible_eq h, loadLoc_eq h, Mem_load_eq h, loadRoot_eq h, Mem_loadBinding_eq h, Mem_loadBindingFor_eq h, Mem_loadElems_eq h, Mem_loadFor_eq h, Mem_loadRun_eq h, Mem_loadSlice_eq h, writeAt_eq h, storeLoc_eq h, Mem_store_eq h, Mem_storeElems_eq h, Mem_storeRun_eq h, normalizeValueForTy_eq h, Store_alloc_eq h, typeDisplay?_eq h, displayNameOfId_eq h, displayNameOf_eq h, goTypeNameForMessage_eq h, payloadDynamicTypeNote_eq h, abortRefusal_eq h, methodCarrierKey?_eq h, interfaceDeclaredMethods?_eq h, defaultValue_eq h, allocDecls_eq h, atomicStore_eq h, applyAtomicOp_eq h, applyChanOp_eq h, tyUncomparable_eq h, valueHashability_eq h, checkKeyHashable_eq h, valueEq_eq h, mapEntryIndex?_eq h, mapLookupValue_eq h, commitClause_eq h, applySelectCore_eq h, applySelect_eq h, applySlice_eq h, buildArrayValue_eq h, buildDefaultArrayValue_eq h, mapAssignValue_plan_eq h, applyStmtOpCore_plan_eq h, buildAppendBackingValue_eq h, applyStmtOp_plan_eq h, buildStructFields_eq h, buildStructValue_eq h, convertValueToTy_eq h, indexTargetLoc_eq h]

theorem convCapApplyAt_free (c : ProgramCtx) : @convCapApplyAt c = @convCapApplyAt c.tablesFree := rfl
theorem convCapApplyAt_eq (h : a.tablesFree = b.tablesFree) : @convCapApplyAt a = @convCapApplyAt b := by
  rw [convCapApplyAt_free a, convCapApplyAt_free b, h]

theorem convCapApply_free (c : ProgramCtx) : @convCapApply c = @convCapApply c.tablesFree := rfl
theorem convCapApply_eq (h : a.tablesFree = b.tablesFree) : @convCapApply a = @convCapApply b := by
  rw [convCapApply_free a, convCapApply_free b, h]

theorem syncCell_eq (h : a.tablesFree = b.tablesFree) : @syncCell a = @syncCell b := by
  delta syncCell; simp only [types_eq h, typeDisplays_eq h, globals_eq h, structTagCompatible_eq h, loadLoc_eq h, Mem_load_eq h, loadRoot_eq h, Mem_loadBinding_eq h, Mem_loadBindingFor_eq h, Mem_loadElems_eq h, Mem_loadFor_eq h, Mem_loadRun_eq h, Mem_loadSlice_eq h, writeAt_eq h, storeLoc_eq h, Mem_store_eq h, Mem_storeElems_eq h, Mem_storeRun_eq h, normalizeValueForTy_eq h, Store_alloc_eq h, typeDisplay?_eq h, displayNameOfId_eq h, displayNameOf_eq h, goTypeNameForMessage_eq h, payloadDynamicTypeNote_eq h, abortRefusal_eq h, methodCarrierKey?_eq h, interfaceDeclaredMethods?_eq h, defaultValue_eq h, allocDecls_eq h, atomicStore_eq h, applyAtomicOp_eq h, applyChanOp_eq h, tyUncomparable_eq h, valueHashability_eq h, checkKeyHashable_eq h, valueEq_eq h, mapEntryIndex?_eq h, mapLookupValue_eq h, commitClause_eq h, applySelectCore_eq h, applySelect_eq h, applySlice_eq h, buildArrayValue_eq h, buildDefaultArrayValue_eq h, mapAssignValue_plan_eq h, applyStmtOpCore_plan_eq h, buildAppendBackingValue_eq h, applyStmtOp_plan_eq h, buildStructFields_eq h, buildStructValue_eq h, convertValueToTy_eq h, indexTargetLoc_eq h, dynamicTypeNameForMessage_eq h, convCapApplyAt_eq h, convCapApply_eq h]

theorem applySyncOpCore_eq (h : a.tablesFree = b.tablesFree) : @applySyncOpCore a = @applySyncOpCore b := by
  delta applySyncOpCore; simp only [types_eq h, typeDisplays_eq h, globals_eq h, structTagCompatible_eq h, loadLoc_eq h, Mem_load_eq h, loadRoot_eq h, Mem_loadBinding_eq h, Mem_loadBindingFor_eq h, Mem_loadElems_eq h, Mem_loadFor_eq h, Mem_loadRun_eq h, Mem_loadSlice_eq h, writeAt_eq h, storeLoc_eq h, Mem_store_eq h, Mem_storeElems_eq h, Mem_storeRun_eq h, normalizeValueForTy_eq h, Store_alloc_eq h, typeDisplay?_eq h, displayNameOfId_eq h, displayNameOf_eq h, goTypeNameForMessage_eq h, payloadDynamicTypeNote_eq h, abortRefusal_eq h, methodCarrierKey?_eq h, interfaceDeclaredMethods?_eq h, defaultValue_eq h, allocDecls_eq h, atomicStore_eq h, applyAtomicOp_eq h, applyChanOp_eq h, tyUncomparable_eq h, valueHashability_eq h, checkKeyHashable_eq h, valueEq_eq h, mapEntryIndex?_eq h, mapLookupValue_eq h, commitClause_eq h, applySelectCore_eq h, applySelect_eq h, applySlice_eq h, buildArrayValue_eq h, buildDefaultArrayValue_eq h, mapAssignValue_plan_eq h, applyStmtOpCore_plan_eq h, buildAppendBackingValue_eq h, applyStmtOp_plan_eq h, buildStructFields_eq h, buildStructValue_eq h, convertValueToTy_eq h, indexTargetLoc_eq h, dynamicTypeNameForMessage_eq h, convCapApplyAt_eq h, convCapApply_eq h, syncCell_eq h]

theorem applyTryLock_eq (h : a.tablesFree = b.tablesFree) : @applyTryLock a = @applyTryLock b := by
  delta applyTryLock; simp only [types_eq h, typeDisplays_eq h, globals_eq h, structTagCompatible_eq h, loadLoc_eq h, Mem_load_eq h, loadRoot_eq h, Mem_loadBinding_eq h, Mem_loadBindingFor_eq h, Mem_loadElems_eq h, Mem_loadFor_eq h, Mem_loadRun_eq h, Mem_loadSlice_eq h, writeAt_eq h, storeLoc_eq h, Mem_store_eq h, Mem_storeElems_eq h, Mem_storeRun_eq h, normalizeValueForTy_eq h, Store_alloc_eq h, typeDisplay?_eq h, displayNameOfId_eq h, displayNameOf_eq h, goTypeNameForMessage_eq h, payloadDynamicTypeNote_eq h, abortRefusal_eq h, methodCarrierKey?_eq h, interfaceDeclaredMethods?_eq h, defaultValue_eq h, allocDecls_eq h, atomicStore_eq h, applyAtomicOp_eq h, applyChanOp_eq h, tyUncomparable_eq h, valueHashability_eq h, checkKeyHashable_eq h, valueEq_eq h, mapEntryIndex?_eq h, mapLookupValue_eq h, commitClause_eq h, applySelectCore_eq h, applySelect_eq h, applySlice_eq h, buildArrayValue_eq h, buildDefaultArrayValue_eq h, mapAssignValue_plan_eq h, applyStmtOpCore_plan_eq h, buildAppendBackingValue_eq h, applyStmtOp_plan_eq h, buildStructFields_eq h, buildStructValue_eq h, convertValueToTy_eq h, indexTargetLoc_eq h, dynamicTypeNameForMessage_eq h, convCapApplyAt_eq h, convCapApply_eq h, syncCell_eq h, applySyncOpCore_eq h]

theorem applySyncOp_eq (h : a.tablesFree = b.tablesFree) : @applySyncOp a = @applySyncOp b := by
  delta applySyncOp; simp only [types_eq h, typeDisplays_eq h, globals_eq h, structTagCompatible_eq h, loadLoc_eq h, Mem_load_eq h, loadRoot_eq h, Mem_loadBinding_eq h, Mem_loadBindingFor_eq h, Mem_loadElems_eq h, Mem_loadFor_eq h, Mem_loadRun_eq h, Mem_loadSlice_eq h, writeAt_eq h, storeLoc_eq h, Mem_store_eq h, Mem_storeElems_eq h, Mem_storeRun_eq h, normalizeValueForTy_eq h, Store_alloc_eq h, typeDisplay?_eq h, displayNameOfId_eq h, displayNameOf_eq h, goTypeNameForMessage_eq h, payloadDynamicTypeNote_eq h, abortRefusal_eq h, methodCarrierKey?_eq h, interfaceDeclaredMethods?_eq h, defaultValue_eq h, allocDecls_eq h, atomicStore_eq h, applyAtomicOp_eq h, applyChanOp_eq h, tyUncomparable_eq h, valueHashability_eq h, checkKeyHashable_eq h, valueEq_eq h, mapEntryIndex?_eq h, mapLookupValue_eq h, commitClause_eq h, applySelectCore_eq h, applySelect_eq h, applySlice_eq h, buildArrayValue_eq h, buildDefaultArrayValue_eq h, mapAssignValue_plan_eq h, applyStmtOpCore_plan_eq h, buildAppendBackingValue_eq h, applyStmtOp_plan_eq h, buildStructFields_eq h, buildStructValue_eq h, convertValueToTy_eq h, indexTargetLoc_eq h, dynamicTypeNameForMessage_eq h, convCapApplyAt_eq h, convCapApply_eq h, syncCell_eq h, applySyncOpCore_eq h, applyTryLock_eq h]

theorem bindIterVars_free (c : ProgramCtx) : @bindIterVars c = @bindIterVars c.tablesFree := rfl
theorem bindIterVars_eq (h : a.tablesFree = b.tablesFree) : @bindIterVars a = @bindIterVars b := by
  rw [bindIterVars_free a, bindIterVars_free b, h]

theorem bindParams_eq_app (h : a.tablesFree = b.tablesFree) (env : LocalEnv) (s : Store) (ps : List Param) (vs : List GoValue) :
    bindParams a env s ps vs = bindParams b env s ps vs := by
  fun_induction bindParams a env s ps vs <;> (try simp only [types_eq h, typeDisplays_eq h, globals_eq h, structTagCompatible_eq h, loadLoc_eq h, Mem_load_eq h, loadRoot_eq h, Mem_loadBinding_eq h, Mem_loadBindingFor_eq h, Mem_loadElems_eq h, Mem_loadFor_eq h, Mem_loadRun_eq h, Mem_loadSlice_eq h, writeAt_eq h, storeLoc_eq h, Mem_store_eq h, Mem_storeElems_eq h, Mem_storeRun_eq h, normalizeValueForTy_eq h, Store_alloc_eq h, typeDisplay?_eq h, displayNameOfId_eq h, displayNameOf_eq h, goTypeNameForMessage_eq h, payloadDynamicTypeNote_eq h, abortRefusal_eq h, methodCarrierKey?_eq h, interfaceDeclaredMethods?_eq h, defaultValue_eq h, allocDecls_eq h, atomicStore_eq h, applyAtomicOp_eq h, applyChanOp_eq h, tyUncomparable_eq h, valueHashability_eq h, checkKeyHashable_eq h, valueEq_eq h, mapEntryIndex?_eq h, mapLookupValue_eq h, commitClause_eq h, applySelectCore_eq h, applySelect_eq h, applySlice_eq h, buildArrayValue_eq h, buildDefaultArrayValue_eq h, mapAssignValue_plan_eq h, applyStmtOpCore_plan_eq h, buildAppendBackingValue_eq h, applyStmtOp_plan_eq h, buildStructFields_eq h, buildStructValue_eq h, convertValueToTy_eq h, indexTargetLoc_eq h, dynamicTypeNameForMessage_eq h, convCapApplyAt_eq h, convCapApply_eq h, syncCell_eq h, applySyncOpCore_eq h, applyTryLock_eq h, applySyncOp_eq h, bindIterVars_eq h] at *) <;> simp +zetaDelta only [bindParams, types_eq h, typeDisplays_eq h, globals_eq h, structTagCompatible_eq h, loadLoc_eq h, Mem_load_eq h, loadRoot_eq h, Mem_loadBinding_eq h, Mem_loadBindingFor_eq h, Mem_loadElems_eq h, Mem_loadFor_eq h, Mem_loadRun_eq h, Mem_loadSlice_eq h, writeAt_eq h, storeLoc_eq h, Mem_store_eq h, Mem_storeElems_eq h, Mem_storeRun_eq h, normalizeValueForTy_eq h, Store_alloc_eq h, typeDisplay?_eq h, displayNameOfId_eq h, displayNameOf_eq h, goTypeNameForMessage_eq h, payloadDynamicTypeNote_eq h, abortRefusal_eq h, methodCarrierKey?_eq h, interfaceDeclaredMethods?_eq h, defaultValue_eq h, allocDecls_eq h, atomicStore_eq h, applyAtomicOp_eq h, applyChanOp_eq h, tyUncomparable_eq h, valueHashability_eq h, checkKeyHashable_eq h, valueEq_eq h, mapEntryIndex?_eq h, mapLookupValue_eq h, commitClause_eq h, applySelectCore_eq h, applySelect_eq h, applySlice_eq h, buildArrayValue_eq h, buildDefaultArrayValue_eq h, mapAssignValue_plan_eq h, applyStmtOpCore_plan_eq h, buildAppendBackingValue_eq h, applyStmtOp_plan_eq h, buildStructFields_eq h, buildStructValue_eq h, convertValueToTy_eq h, indexTargetLoc_eq h, dynamicTypeNameForMessage_eq h, convCapApplyAt_eq h, convCapApply_eq h, syncCell_eq h, applySyncOpCore_eq h, applyTryLock_eq h, applySyncOp_eq h, bindIterVars_eq h, *]
  all_goals (try (split <;> simp_all))
theorem bindParams_eq (h : a.tablesFree = b.tablesFree) : @bindParams a = @bindParams b := by
  funext env s ps vs; exact bindParams_eq_app h env s ps vs

theorem structFieldValue_free (c : ProgramCtx) : @structFieldValue c = @structFieldValue c.tablesFree := rfl
theorem structFieldValue_eq (h : a.tablesFree = b.tablesFree) : @structFieldValue a = @structFieldValue b := by
  rw [structFieldValue_free a, structFieldValue_free b, h]

theorem promotionHop_eq (h : a.tablesFree = b.tablesFree) : @promotionHop a = @promotionHop b := by
  delta promotionHop; simp only [types_eq h, typeDisplays_eq h, globals_eq h, structTagCompatible_eq h, loadLoc_eq h, Mem_load_eq h, loadRoot_eq h, Mem_loadBinding_eq h, Mem_loadBindingFor_eq h, Mem_loadElems_eq h, Mem_loadFor_eq h, Mem_loadRun_eq h, Mem_loadSlice_eq h, writeAt_eq h, storeLoc_eq h, Mem_store_eq h, Mem_storeElems_eq h, Mem_storeRun_eq h, normalizeValueForTy_eq h, Store_alloc_eq h, typeDisplay?_eq h, displayNameOfId_eq h, displayNameOf_eq h, goTypeNameForMessage_eq h, payloadDynamicTypeNote_eq h, abortRefusal_eq h, methodCarrierKey?_eq h, interfaceDeclaredMethods?_eq h, defaultValue_eq h, allocDecls_eq h, atomicStore_eq h, applyAtomicOp_eq h, applyChanOp_eq h, tyUncomparable_eq h, valueHashability_eq h, checkKeyHashable_eq h, valueEq_eq h, mapEntryIndex?_eq h, mapLookupValue_eq h, commitClause_eq h, applySelectCore_eq h, applySelect_eq h, applySlice_eq h, buildArrayValue_eq h, buildDefaultArrayValue_eq h, mapAssignValue_plan_eq h, applyStmtOpCore_plan_eq h, buildAppendBackingValue_eq h, applyStmtOp_plan_eq h, buildStructFields_eq h, buildStructValue_eq h, convertValueToTy_eq h, indexTargetLoc_eq h, dynamicTypeNameForMessage_eq h, convCapApplyAt_eq h, convCapApply_eq h, syncCell_eq h, applySyncOpCore_eq h, applyTryLock_eq h, applySyncOp_eq h, bindIterVars_eq h, bindParams_eq h, structFieldValue_eq h]

theorem promotionWalk_eq_app (h : a.tablesFree = b.tablesFree) (s : Store) (cur : WalkCursor) (hs : List PromotionHop) :
    promotionWalk a s cur hs = promotionWalk b s cur hs := by
  fun_induction promotionWalk a s cur hs <;> (try simp only [types_eq h, typeDisplays_eq h, globals_eq h, structTagCompatible_eq h, loadLoc_eq h, Mem_load_eq h, loadRoot_eq h, Mem_loadBinding_eq h, Mem_loadBindingFor_eq h, Mem_loadElems_eq h, Mem_loadFor_eq h, Mem_loadRun_eq h, Mem_loadSlice_eq h, writeAt_eq h, storeLoc_eq h, Mem_store_eq h, Mem_storeElems_eq h, Mem_storeRun_eq h, normalizeValueForTy_eq h, Store_alloc_eq h, typeDisplay?_eq h, displayNameOfId_eq h, displayNameOf_eq h, goTypeNameForMessage_eq h, payloadDynamicTypeNote_eq h, abortRefusal_eq h, methodCarrierKey?_eq h, interfaceDeclaredMethods?_eq h, defaultValue_eq h, allocDecls_eq h, atomicStore_eq h, applyAtomicOp_eq h, applyChanOp_eq h, tyUncomparable_eq h, valueHashability_eq h, checkKeyHashable_eq h, valueEq_eq h, mapEntryIndex?_eq h, mapLookupValue_eq h, commitClause_eq h, applySelectCore_eq h, applySelect_eq h, applySlice_eq h, buildArrayValue_eq h, buildDefaultArrayValue_eq h, mapAssignValue_plan_eq h, applyStmtOpCore_plan_eq h, buildAppendBackingValue_eq h, applyStmtOp_plan_eq h, buildStructFields_eq h, buildStructValue_eq h, convertValueToTy_eq h, indexTargetLoc_eq h, dynamicTypeNameForMessage_eq h, convCapApplyAt_eq h, convCapApply_eq h, syncCell_eq h, applySyncOpCore_eq h, applyTryLock_eq h, applySyncOp_eq h, bindIterVars_eq h, bindParams_eq h, structFieldValue_eq h, promotionHop_eq h] at *) <;> simp +zetaDelta only [promotionWalk, types_eq h, typeDisplays_eq h, globals_eq h, structTagCompatible_eq h, loadLoc_eq h, Mem_load_eq h, loadRoot_eq h, Mem_loadBinding_eq h, Mem_loadBindingFor_eq h, Mem_loadElems_eq h, Mem_loadFor_eq h, Mem_loadRun_eq h, Mem_loadSlice_eq h, writeAt_eq h, storeLoc_eq h, Mem_store_eq h, Mem_storeElems_eq h, Mem_storeRun_eq h, normalizeValueForTy_eq h, Store_alloc_eq h, typeDisplay?_eq h, displayNameOfId_eq h, displayNameOf_eq h, goTypeNameForMessage_eq h, payloadDynamicTypeNote_eq h, abortRefusal_eq h, methodCarrierKey?_eq h, interfaceDeclaredMethods?_eq h, defaultValue_eq h, allocDecls_eq h, atomicStore_eq h, applyAtomicOp_eq h, applyChanOp_eq h, tyUncomparable_eq h, valueHashability_eq h, checkKeyHashable_eq h, valueEq_eq h, mapEntryIndex?_eq h, mapLookupValue_eq h, commitClause_eq h, applySelectCore_eq h, applySelect_eq h, applySlice_eq h, buildArrayValue_eq h, buildDefaultArrayValue_eq h, mapAssignValue_plan_eq h, applyStmtOpCore_plan_eq h, buildAppendBackingValue_eq h, applyStmtOp_plan_eq h, buildStructFields_eq h, buildStructValue_eq h, convertValueToTy_eq h, indexTargetLoc_eq h, dynamicTypeNameForMessage_eq h, convCapApplyAt_eq h, convCapApply_eq h, syncCell_eq h, applySyncOpCore_eq h, applyTryLock_eq h, applySyncOp_eq h, bindIterVars_eq h, bindParams_eq h, structFieldValue_eq h, promotionHop_eq h, *]
  all_goals (try (split <;> simp_all))
theorem promotionWalk_eq (h : a.tablesFree = b.tablesFree) : @promotionWalk a = @promotionWalk b := by
  funext s cur hs; exact promotionWalk_eq_app h s cur hs

theorem receiverAt_eq (h : a.tablesFree = b.tablesFree) : @receiverAt a = @receiverAt b := by
  delta receiverAt; simp only [types_eq h, typeDisplays_eq h, globals_eq h, structTagCompatible_eq h, loadLoc_eq h, Mem_load_eq h, loadRoot_eq h, Mem_loadBinding_eq h, Mem_loadBindingFor_eq h, Mem_loadElems_eq h, Mem_loadFor_eq h, Mem_loadRun_eq h, Mem_loadSlice_eq h, writeAt_eq h, storeLoc_eq h, Mem_store_eq h, Mem_storeElems_eq h, Mem_storeRun_eq h, normalizeValueForTy_eq h, Store_alloc_eq h, typeDisplay?_eq h, displayNameOfId_eq h, displayNameOf_eq h, goTypeNameForMessage_eq h, payloadDynamicTypeNote_eq h, abortRefusal_eq h, methodCarrierKey?_eq h, interfaceDeclaredMethods?_eq h, defaultValue_eq h, allocDecls_eq h, atomicStore_eq h, applyAtomicOp_eq h, applyChanOp_eq h, tyUncomparable_eq h, valueHashability_eq h, checkKeyHashable_eq h, valueEq_eq h, mapEntryIndex?_eq h, mapLookupValue_eq h, commitClause_eq h, applySelectCore_eq h, applySelect_eq h, applySlice_eq h, buildArrayValue_eq h, buildDefaultArrayValue_eq h, mapAssignValue_plan_eq h, applyStmtOpCore_plan_eq h, buildAppendBackingValue_eq h, applyStmtOp_plan_eq h, buildStructFields_eq h, buildStructValue_eq h, convertValueToTy_eq h, indexTargetLoc_eq h, dynamicTypeNameForMessage_eq h, convCapApplyAt_eq h, convCapApply_eq h, syncCell_eq h, applySyncOpCore_eq h, applyTryLock_eq h, applySyncOp_eq h, bindIterVars_eq h, bindParams_eq h, structFieldValue_eq h, promotionHop_eq h, promotionWalk_eq h]

theorem symbolKeyForMessage_eq (h : a.tablesFree = b.tablesFree) : @symbolKeyForMessage a = @symbolKeyForMessage b := by
  delta symbolKeyForMessage; simp only [types_eq h, typeDisplays_eq h, globals_eq h, structTagCompatible_eq h, loadLoc_eq h, Mem_load_eq h, loadRoot_eq h, Mem_loadBinding_eq h, Mem_loadBindingFor_eq h, Mem_loadElems_eq h, Mem_loadFor_eq h, Mem_loadRun_eq h, Mem_loadSlice_eq h, writeAt_eq h, storeLoc_eq h, Mem_store_eq h, Mem_storeElems_eq h, Mem_storeRun_eq h, normalizeValueForTy_eq h, Store_alloc_eq h, typeDisplay?_eq h, displayNameOfId_eq h, displayNameOf_eq h, goTypeNameForMessage_eq h, payloadDynamicTypeNote_eq h, abortRefusal_eq h, methodCarrierKey?_eq h, interfaceDeclaredMethods?_eq h, defaultValue_eq h, allocDecls_eq h, atomicStore_eq h, applyAtomicOp_eq h, applyChanOp_eq h, tyUncomparable_eq h, valueHashability_eq h, checkKeyHashable_eq h, valueEq_eq h, mapEntryIndex?_eq h, mapLookupValue_eq h, commitClause_eq h, applySelectCore_eq h, applySelect_eq h, applySlice_eq h, buildArrayValue_eq h, buildDefaultArrayValue_eq h, mapAssignValue_plan_eq h, applyStmtOpCore_plan_eq h, buildAppendBackingValue_eq h, applyStmtOp_plan_eq h, buildStructFields_eq h, buildStructValue_eq h, convertValueToTy_eq h, indexTargetLoc_eq h, dynamicTypeNameForMessage_eq h, convCapApplyAt_eq h, convCapApply_eq h, syncCell_eq h, applySyncOpCore_eq h, applyTryLock_eq h, applySyncOp_eq h, bindIterVars_eq h, bindParams_eq h, structFieldValue_eq h, promotionHop_eq h, promotionWalk_eq h, receiverAt_eq h]

theorem loadResults_eq_app (h : a.tablesFree = b.tablesFree) (s : Store) (locs : List Loc) :
    loadResults a s locs = loadResults b s locs := by
  fun_induction loadResults a s locs <;> (try simp only [types_eq h, typeDisplays_eq h, globals_eq h, structTagCompatible_eq h, loadLoc_eq h, Mem_load_eq h, loadRoot_eq h, Mem_loadBinding_eq h, Mem_loadBindingFor_eq h, Mem_loadElems_eq h, Mem_loadFor_eq h, Mem_loadRun_eq h, Mem_loadSlice_eq h, writeAt_eq h, storeLoc_eq h, Mem_store_eq h, Mem_storeElems_eq h, Mem_storeRun_eq h, normalizeValueForTy_eq h, Store_alloc_eq h, typeDisplay?_eq h, displayNameOfId_eq h, displayNameOf_eq h, goTypeNameForMessage_eq h, payloadDynamicTypeNote_eq h, abortRefusal_eq h, methodCarrierKey?_eq h, interfaceDeclaredMethods?_eq h, defaultValue_eq h, allocDecls_eq h, atomicStore_eq h, applyAtomicOp_eq h, applyChanOp_eq h, tyUncomparable_eq h, valueHashability_eq h, checkKeyHashable_eq h, valueEq_eq h, mapEntryIndex?_eq h, mapLookupValue_eq h, commitClause_eq h, applySelectCore_eq h, applySelect_eq h, applySlice_eq h, buildArrayValue_eq h, buildDefaultArrayValue_eq h, mapAssignValue_plan_eq h, applyStmtOpCore_plan_eq h, buildAppendBackingValue_eq h, applyStmtOp_plan_eq h, buildStructFields_eq h, buildStructValue_eq h, convertValueToTy_eq h, indexTargetLoc_eq h, dynamicTypeNameForMessage_eq h, convCapApplyAt_eq h, convCapApply_eq h, syncCell_eq h, applySyncOpCore_eq h, applyTryLock_eq h, applySyncOp_eq h, bindIterVars_eq h, bindParams_eq h, structFieldValue_eq h, promotionHop_eq h, promotionWalk_eq h, receiverAt_eq h, symbolKeyForMessage_eq h] at *) <;> simp +zetaDelta only [loadResults, types_eq h, typeDisplays_eq h, globals_eq h, structTagCompatible_eq h, loadLoc_eq h, Mem_load_eq h, loadRoot_eq h, Mem_loadBinding_eq h, Mem_loadBindingFor_eq h, Mem_loadElems_eq h, Mem_loadFor_eq h, Mem_loadRun_eq h, Mem_loadSlice_eq h, writeAt_eq h, storeLoc_eq h, Mem_store_eq h, Mem_storeElems_eq h, Mem_storeRun_eq h, normalizeValueForTy_eq h, Store_alloc_eq h, typeDisplay?_eq h, displayNameOfId_eq h, displayNameOf_eq h, goTypeNameForMessage_eq h, payloadDynamicTypeNote_eq h, abortRefusal_eq h, methodCarrierKey?_eq h, interfaceDeclaredMethods?_eq h, defaultValue_eq h, allocDecls_eq h, atomicStore_eq h, applyAtomicOp_eq h, applyChanOp_eq h, tyUncomparable_eq h, valueHashability_eq h, checkKeyHashable_eq h, valueEq_eq h, mapEntryIndex?_eq h, mapLookupValue_eq h, commitClause_eq h, applySelectCore_eq h, applySelect_eq h, applySlice_eq h, buildArrayValue_eq h, buildDefaultArrayValue_eq h, mapAssignValue_plan_eq h, applyStmtOpCore_plan_eq h, buildAppendBackingValue_eq h, applyStmtOp_plan_eq h, buildStructFields_eq h, buildStructValue_eq h, convertValueToTy_eq h, indexTargetLoc_eq h, dynamicTypeNameForMessage_eq h, convCapApplyAt_eq h, convCapApply_eq h, syncCell_eq h, applySyncOpCore_eq h, applyTryLock_eq h, applySyncOp_eq h, bindIterVars_eq h, bindParams_eq h, structFieldValue_eq h, promotionHop_eq h, promotionWalk_eq h, receiverAt_eq h, symbolKeyForMessage_eq h, *]
  all_goals (try (split <;> simp_all))
theorem loadResults_eq (h : a.tablesFree = b.tablesFree) : @loadResults a = @loadResults b := by
  funext s locs; exact loadResults_eq_app h s locs

theorem mapIterCandidates_free (c : ProgramCtx) : @mapIterCandidates c = @mapIterCandidates c.tablesFree := rfl
theorem mapIterCandidates_eq (h : a.tablesFree = b.tablesFree) : @mapIterCandidates a = @mapIterCandidates b := by
  rw [mapIterCandidates_free a, mapIterCandidates_free b, h]

theorem preprintFatalStop_eq (h : a.tablesFree = b.tablesFree) : @preprintFatalStop a = @preprintFatalStop b := by
  delta preprintFatalStop; simp only [types_eq h, typeDisplays_eq h, globals_eq h, structTagCompatible_eq h, loadLoc_eq h, Mem_load_eq h, loadRoot_eq h, Mem_loadBinding_eq h, Mem_loadBindingFor_eq h, Mem_loadElems_eq h, Mem_loadFor_eq h, Mem_loadRun_eq h, Mem_loadSlice_eq h, writeAt_eq h, storeLoc_eq h, Mem_store_eq h, Mem_storeElems_eq h, Mem_storeRun_eq h, normalizeValueForTy_eq h, Store_alloc_eq h, typeDisplay?_eq h, displayNameOfId_eq h, displayNameOf_eq h, goTypeNameForMessage_eq h, payloadDynamicTypeNote_eq h, abortRefusal_eq h, methodCarrierKey?_eq h, interfaceDeclaredMethods?_eq h, defaultValue_eq h, allocDecls_eq h, atomicStore_eq h, applyAtomicOp_eq h, applyChanOp_eq h, tyUncomparable_eq h, valueHashability_eq h, checkKeyHashable_eq h, valueEq_eq h, mapEntryIndex?_eq h, mapLookupValue_eq h, commitClause_eq h, applySelectCore_eq h, applySelect_eq h, applySlice_eq h, buildArrayValue_eq h, buildDefaultArrayValue_eq h, mapAssignValue_plan_eq h, applyStmtOpCore_plan_eq h, buildAppendBackingValue_eq h, applyStmtOp_plan_eq h, buildStructFields_eq h, buildStructValue_eq h, convertValueToTy_eq h, indexTargetLoc_eq h, dynamicTypeNameForMessage_eq h, convCapApplyAt_eq h, convCapApply_eq h, syncCell_eq h, applySyncOpCore_eq h, applyTryLock_eq h, applySyncOp_eq h, bindIterVars_eq h, bindParams_eq h, structFieldValue_eq h, promotionHop_eq h, promotionWalk_eq h, receiverAt_eq h, symbolKeyForMessage_eq h, loadResults_eq h, mapIterCandidates_eq h]

theorem panicUnwindStop_eq (h : a.tablesFree = b.tablesFree) : @panicUnwindStop a = @panicUnwindStop b := by
  delta panicUnwindStop; simp only [types_eq h, typeDisplays_eq h, globals_eq h, structTagCompatible_eq h, loadLoc_eq h, Mem_load_eq h, loadRoot_eq h, Mem_loadBinding_eq h, Mem_loadBindingFor_eq h, Mem_loadElems_eq h, Mem_loadFor_eq h, Mem_loadRun_eq h, Mem_loadSlice_eq h, writeAt_eq h, storeLoc_eq h, Mem_store_eq h, Mem_storeElems_eq h, Mem_storeRun_eq h, normalizeValueForTy_eq h, Store_alloc_eq h, typeDisplay?_eq h, displayNameOfId_eq h, displayNameOf_eq h, goTypeNameForMessage_eq h, payloadDynamicTypeNote_eq h, abortRefusal_eq h, methodCarrierKey?_eq h, interfaceDeclaredMethods?_eq h, defaultValue_eq h, allocDecls_eq h, atomicStore_eq h, applyAtomicOp_eq h, applyChanOp_eq h, tyUncomparable_eq h, valueHashability_eq h, checkKeyHashable_eq h, valueEq_eq h, mapEntryIndex?_eq h, mapLookupValue_eq h, commitClause_eq h, applySelectCore_eq h, applySelect_eq h, applySlice_eq h, buildArrayValue_eq h, buildDefaultArrayValue_eq h, mapAssignValue_plan_eq h, applyStmtOpCore_plan_eq h, buildAppendBackingValue_eq h, applyStmtOp_plan_eq h, buildStructFields_eq h, buildStructValue_eq h, convertValueToTy_eq h, indexTargetLoc_eq h, dynamicTypeNameForMessage_eq h, convCapApplyAt_eq h, convCapApply_eq h, syncCell_eq h, applySyncOpCore_eq h, applyTryLock_eq h, applySyncOp_eq h, bindIterVars_eq h, bindParams_eq h, structFieldValue_eq h, promotionHop_eq h, promotionWalk_eq h, receiverAt_eq h, symbolKeyForMessage_eq h, loadResults_eq h, mapIterCandidates_eq h, preprintFatalStop_eq h]

theorem projChainTarget_eq_app (h : a.tablesFree = b.tablesFree) (s : Store) (k : Cont) (loc : Loc) :
    projChainTarget a s k loc = projChainTarget b s k loc := by
  fun_induction projChainTarget a s k loc <;> (try simp only [types_eq h, typeDisplays_eq h, globals_eq h, structTagCompatible_eq h, loadLoc_eq h, Mem_load_eq h, loadRoot_eq h, Mem_loadBinding_eq h, Mem_loadBindingFor_eq h, Mem_loadElems_eq h, Mem_loadFor_eq h, Mem_loadRun_eq h, Mem_loadSlice_eq h, writeAt_eq h, storeLoc_eq h, Mem_store_eq h, Mem_storeElems_eq h, Mem_storeRun_eq h, normalizeValueForTy_eq h, Store_alloc_eq h, typeDisplay?_eq h, displayNameOfId_eq h, displayNameOf_eq h, goTypeNameForMessage_eq h, payloadDynamicTypeNote_eq h, abortRefusal_eq h, methodCarrierKey?_eq h, interfaceDeclaredMethods?_eq h, defaultValue_eq h, allocDecls_eq h, atomicStore_eq h, applyAtomicOp_eq h, applyChanOp_eq h, tyUncomparable_eq h, valueHashability_eq h, checkKeyHashable_eq h, valueEq_eq h, mapEntryIndex?_eq h, mapLookupValue_eq h, commitClause_eq h, applySelectCore_eq h, applySelect_eq h, applySlice_eq h, buildArrayValue_eq h, buildDefaultArrayValue_eq h, mapAssignValue_plan_eq h, applyStmtOpCore_plan_eq h, buildAppendBackingValue_eq h, applyStmtOp_plan_eq h, buildStructFields_eq h, buildStructValue_eq h, convertValueToTy_eq h, indexTargetLoc_eq h, dynamicTypeNameForMessage_eq h, convCapApplyAt_eq h, convCapApply_eq h, syncCell_eq h, applySyncOpCore_eq h, applyTryLock_eq h, applySyncOp_eq h, bindIterVars_eq h, bindParams_eq h, structFieldValue_eq h, promotionHop_eq h, promotionWalk_eq h, receiverAt_eq h, symbolKeyForMessage_eq h, loadResults_eq h, mapIterCandidates_eq h, preprintFatalStop_eq h, panicUnwindStop_eq h] at *) <;> simp +zetaDelta only [projChainTarget, types_eq h, typeDisplays_eq h, globals_eq h, structTagCompatible_eq h, loadLoc_eq h, Mem_load_eq h, loadRoot_eq h, Mem_loadBinding_eq h, Mem_loadBindingFor_eq h, Mem_loadElems_eq h, Mem_loadFor_eq h, Mem_loadRun_eq h, Mem_loadSlice_eq h, writeAt_eq h, storeLoc_eq h, Mem_store_eq h, Mem_storeElems_eq h, Mem_storeRun_eq h, normalizeValueForTy_eq h, Store_alloc_eq h, typeDisplay?_eq h, displayNameOfId_eq h, displayNameOf_eq h, goTypeNameForMessage_eq h, payloadDynamicTypeNote_eq h, abortRefusal_eq h, methodCarrierKey?_eq h, interfaceDeclaredMethods?_eq h, defaultValue_eq h, allocDecls_eq h, atomicStore_eq h, applyAtomicOp_eq h, applyChanOp_eq h, tyUncomparable_eq h, valueHashability_eq h, checkKeyHashable_eq h, valueEq_eq h, mapEntryIndex?_eq h, mapLookupValue_eq h, commitClause_eq h, applySelectCore_eq h, applySelect_eq h, applySlice_eq h, buildArrayValue_eq h, buildDefaultArrayValue_eq h, mapAssignValue_plan_eq h, applyStmtOpCore_plan_eq h, buildAppendBackingValue_eq h, applyStmtOp_plan_eq h, buildStructFields_eq h, buildStructValue_eq h, convertValueToTy_eq h, indexTargetLoc_eq h, dynamicTypeNameForMessage_eq h, convCapApplyAt_eq h, convCapApply_eq h, syncCell_eq h, applySyncOpCore_eq h, applyTryLock_eq h, applySyncOp_eq h, bindIterVars_eq h, bindParams_eq h, structFieldValue_eq h, promotionHop_eq h, promotionWalk_eq h, receiverAt_eq h, symbolKeyForMessage_eq h, loadResults_eq h, mapIterCandidates_eq h, preprintFatalStop_eq h, panicUnwindStop_eq h, *]
  all_goals (try (split <;> simp_all))
theorem projChainTarget_eq (h : a.tablesFree = b.tablesFree) : @projChainTarget a = @projChainTarget b := by
  funext s k loc; exact projChainTarget_eq_app h s k loc

theorem resolveChain_eq_app (h : a.tablesFree = b.tablesFree) (s : Store) (cur : GoValue) (steps : List TargetStep) (idxs : List GoValue) :
    resolveChain a s cur steps idxs = resolveChain b s cur steps idxs := by
  fun_induction resolveChain a s cur steps idxs <;> (try simp only [types_eq h, typeDisplays_eq h, globals_eq h, structTagCompatible_eq h, loadLoc_eq h, Mem_load_eq h, loadRoot_eq h, Mem_loadBinding_eq h, Mem_loadBindingFor_eq h, Mem_loadElems_eq h, Mem_loadFor_eq h, Mem_loadRun_eq h, Mem_loadSlice_eq h, writeAt_eq h, storeLoc_eq h, Mem_store_eq h, Mem_storeElems_eq h, Mem_storeRun_eq h, normalizeValueForTy_eq h, Store_alloc_eq h, typeDisplay?_eq h, displayNameOfId_eq h, displayNameOf_eq h, goTypeNameForMessage_eq h, payloadDynamicTypeNote_eq h, abortRefusal_eq h, methodCarrierKey?_eq h, interfaceDeclaredMethods?_eq h, defaultValue_eq h, allocDecls_eq h, atomicStore_eq h, applyAtomicOp_eq h, applyChanOp_eq h, tyUncomparable_eq h, valueHashability_eq h, checkKeyHashable_eq h, valueEq_eq h, mapEntryIndex?_eq h, mapLookupValue_eq h, commitClause_eq h, applySelectCore_eq h, applySelect_eq h, applySlice_eq h, buildArrayValue_eq h, buildDefaultArrayValue_eq h, mapAssignValue_plan_eq h, applyStmtOpCore_plan_eq h, buildAppendBackingValue_eq h, applyStmtOp_plan_eq h, buildStructFields_eq h, buildStructValue_eq h, convertValueToTy_eq h, indexTargetLoc_eq h, dynamicTypeNameForMessage_eq h, convCapApplyAt_eq h, convCapApply_eq h, syncCell_eq h, applySyncOpCore_eq h, applyTryLock_eq h, applySyncOp_eq h, bindIterVars_eq h, bindParams_eq h, structFieldValue_eq h, promotionHop_eq h, promotionWalk_eq h, receiverAt_eq h, symbolKeyForMessage_eq h, loadResults_eq h, mapIterCandidates_eq h, preprintFatalStop_eq h, panicUnwindStop_eq h, projChainTarget_eq h] at *) <;> simp +zetaDelta only [resolveChain, types_eq h, typeDisplays_eq h, globals_eq h, structTagCompatible_eq h, loadLoc_eq h, Mem_load_eq h, loadRoot_eq h, Mem_loadBinding_eq h, Mem_loadBindingFor_eq h, Mem_loadElems_eq h, Mem_loadFor_eq h, Mem_loadRun_eq h, Mem_loadSlice_eq h, writeAt_eq h, storeLoc_eq h, Mem_store_eq h, Mem_storeElems_eq h, Mem_storeRun_eq h, normalizeValueForTy_eq h, Store_alloc_eq h, typeDisplay?_eq h, displayNameOfId_eq h, displayNameOf_eq h, goTypeNameForMessage_eq h, payloadDynamicTypeNote_eq h, abortRefusal_eq h, methodCarrierKey?_eq h, interfaceDeclaredMethods?_eq h, defaultValue_eq h, allocDecls_eq h, atomicStore_eq h, applyAtomicOp_eq h, applyChanOp_eq h, tyUncomparable_eq h, valueHashability_eq h, checkKeyHashable_eq h, valueEq_eq h, mapEntryIndex?_eq h, mapLookupValue_eq h, commitClause_eq h, applySelectCore_eq h, applySelect_eq h, applySlice_eq h, buildArrayValue_eq h, buildDefaultArrayValue_eq h, mapAssignValue_plan_eq h, applyStmtOpCore_plan_eq h, buildAppendBackingValue_eq h, applyStmtOp_plan_eq h, buildStructFields_eq h, buildStructValue_eq h, convertValueToTy_eq h, indexTargetLoc_eq h, dynamicTypeNameForMessage_eq h, convCapApplyAt_eq h, convCapApply_eq h, syncCell_eq h, applySyncOpCore_eq h, applyTryLock_eq h, applySyncOp_eq h, bindIterVars_eq h, bindParams_eq h, structFieldValue_eq h, promotionHop_eq h, promotionWalk_eq h, receiverAt_eq h, symbolKeyForMessage_eq h, loadResults_eq h, mapIterCandidates_eq h, preprintFatalStop_eq h, panicUnwindStop_eq h, projChainTarget_eq h, *]
  all_goals (try (split <;> simp_all))
theorem resolveChain_eq (h : a.tablesFree = b.tablesFree) : @resolveChain a = @resolveChain b := by
  funext s cur steps idxs; exact resolveChain_eq_app h s cur steps idxs

theorem stepUnseqEnter_eq (h : a.tablesFree = b.tablesFree) : @stepUnseqEnter a = @stepUnseqEnter b := by
  delta stepUnseqEnter; simp only [types_eq h, typeDisplays_eq h, globals_eq h, structTagCompatible_eq h, loadLoc_eq h, Mem_load_eq h, loadRoot_eq h, Mem_loadBinding_eq h, Mem_loadBindingFor_eq h, Mem_loadElems_eq h, Mem_loadFor_eq h, Mem_loadRun_eq h, Mem_loadSlice_eq h, writeAt_eq h, storeLoc_eq h, Mem_store_eq h, Mem_storeElems_eq h, Mem_storeRun_eq h, normalizeValueForTy_eq h, Store_alloc_eq h, typeDisplay?_eq h, displayNameOfId_eq h, displayNameOf_eq h, goTypeNameForMessage_eq h, payloadDynamicTypeNote_eq h, abortRefusal_eq h, methodCarrierKey?_eq h, interfaceDeclaredMethods?_eq h, defaultValue_eq h, allocDecls_eq h, atomicStore_eq h, applyAtomicOp_eq h, applyChanOp_eq h, tyUncomparable_eq h, valueHashability_eq h, checkKeyHashable_eq h, valueEq_eq h, mapEntryIndex?_eq h, mapLookupValue_eq h, commitClause_eq h, applySelectCore_eq h, applySelect_eq h, applySlice_eq h, buildArrayValue_eq h, buildDefaultArrayValue_eq h, mapAssignValue_plan_eq h, applyStmtOpCore_plan_eq h, buildAppendBackingValue_eq h, applyStmtOp_plan_eq h, buildStructFields_eq h, buildStructValue_eq h, convertValueToTy_eq h, indexTargetLoc_eq h, dynamicTypeNameForMessage_eq h, convCapApplyAt_eq h, convCapApply_eq h, syncCell_eq h, applySyncOpCore_eq h, applyTryLock_eq h, applySyncOp_eq h, bindIterVars_eq h, bindParams_eq h, structFieldValue_eq h, promotionHop_eq h, promotionWalk_eq h, receiverAt_eq h, symbolKeyForMessage_eq h, loadResults_eq h, mapIterCandidates_eq h, preprintFatalStop_eq h, panicUnwindStop_eq h, projChainTarget_eq h, resolveChain_eq h]

theorem unseqGuard_eq (h : a.tablesFree = b.tablesFree) : @unseqGuard a = @unseqGuard b := by
  delta unseqGuard; simp only [types_eq h, typeDisplays_eq h, globals_eq h, structTagCompatible_eq h, loadLoc_eq h, Mem_load_eq h, loadRoot_eq h, Mem_loadBinding_eq h, Mem_loadBindingFor_eq h, Mem_loadElems_eq h, Mem_loadFor_eq h, Mem_loadRun_eq h, Mem_loadSlice_eq h, writeAt_eq h, storeLoc_eq h, Mem_store_eq h, Mem_storeElems_eq h, Mem_storeRun_eq h, normalizeValueForTy_eq h, Store_alloc_eq h, typeDisplay?_eq h, displayNameOfId_eq h, displayNameOf_eq h, goTypeNameForMessage_eq h, payloadDynamicTypeNote_eq h, abortRefusal_eq h, methodCarrierKey?_eq h, interfaceDeclaredMethods?_eq h, defaultValue_eq h, allocDecls_eq h, atomicStore_eq h, applyAtomicOp_eq h, applyChanOp_eq h, tyUncomparable_eq h, valueHashability_eq h, checkKeyHashable_eq h, valueEq_eq h, mapEntryIndex?_eq h, mapLookupValue_eq h, commitClause_eq h, applySelectCore_eq h, applySelect_eq h, applySlice_eq h, buildArrayValue_eq h, buildDefaultArrayValue_eq h, mapAssignValue_plan_eq h, applyStmtOpCore_plan_eq h, buildAppendBackingValue_eq h, applyStmtOp_plan_eq h, buildStructFields_eq h, buildStructValue_eq h, convertValueToTy_eq h, indexTargetLoc_eq h, dynamicTypeNameForMessage_eq h, convCapApplyAt_eq h, convCapApply_eq h, syncCell_eq h, applySyncOpCore_eq h, applyTryLock_eq h, applySyncOp_eq h, bindIterVars_eq h, bindParams_eq h, structFieldValue_eq h, promotionHop_eq h, promotionWalk_eq h, receiverAt_eq h, symbolKeyForMessage_eq h, loadResults_eq h, mapIterCandidates_eq h, preprintFatalStop_eq h, panicUnwindStop_eq h, projChainTarget_eq h, resolveChain_eq h, stepUnseqEnter_eq h]

theorem unseqReadTarget_eq (h : a.tablesFree = b.tablesFree) : @unseqReadTarget a = @unseqReadTarget b := by
  delta unseqReadTarget; simp only [types_eq h, typeDisplays_eq h, globals_eq h, structTagCompatible_eq h, loadLoc_eq h, Mem_load_eq h, loadRoot_eq h, Mem_loadBinding_eq h, Mem_loadBindingFor_eq h, Mem_loadElems_eq h, Mem_loadFor_eq h, Mem_loadRun_eq h, Mem_loadSlice_eq h, writeAt_eq h, storeLoc_eq h, Mem_store_eq h, Mem_storeElems_eq h, Mem_storeRun_eq h, normalizeValueForTy_eq h, Store_alloc_eq h, typeDisplay?_eq h, displayNameOfId_eq h, displayNameOf_eq h, goTypeNameForMessage_eq h, payloadDynamicTypeNote_eq h, abortRefusal_eq h, methodCarrierKey?_eq h, interfaceDeclaredMethods?_eq h, defaultValue_eq h, allocDecls_eq h, atomicStore_eq h, applyAtomicOp_eq h, applyChanOp_eq h, tyUncomparable_eq h, valueHashability_eq h, checkKeyHashable_eq h, valueEq_eq h, mapEntryIndex?_eq h, mapLookupValue_eq h, commitClause_eq h, applySelectCore_eq h, applySelect_eq h, applySlice_eq h, buildArrayValue_eq h, buildDefaultArrayValue_eq h, mapAssignValue_plan_eq h, applyStmtOpCore_plan_eq h, buildAppendBackingValue_eq h, applyStmtOp_plan_eq h, buildStructFields_eq h, buildStructValue_eq h, convertValueToTy_eq h, indexTargetLoc_eq h, dynamicTypeNameForMessage_eq h, convCapApplyAt_eq h, convCapApply_eq h, syncCell_eq h, applySyncOpCore_eq h, applyTryLock_eq h, applySyncOp_eq h, bindIterVars_eq h, bindParams_eq h, structFieldValue_eq h, promotionHop_eq h, promotionWalk_eq h, receiverAt_eq h, symbolKeyForMessage_eq h, loadResults_eq h, mapIterCandidates_eq h, preprintFatalStop_eq h, panicUnwindStop_eq h, projChainTarget_eq h, resolveChain_eq h, stepUnseqEnter_eq h, unseqGuard_eq h]

theorem unseqLoad_plan_eq (h : a.tablesFree = b.tablesFree) : @unseqLoad.plan a = @unseqLoad.plan b := by
  delta unseqLoad.plan; simp only [types_eq h, typeDisplays_eq h, globals_eq h, structTagCompatible_eq h, loadLoc_eq h, Mem_load_eq h, loadRoot_eq h, Mem_loadBinding_eq h, Mem_loadBindingFor_eq h, Mem_loadElems_eq h, Mem_loadFor_eq h, Mem_loadRun_eq h, Mem_loadSlice_eq h, writeAt_eq h, storeLoc_eq h, Mem_store_eq h, Mem_storeElems_eq h, Mem_storeRun_eq h, normalizeValueForTy_eq h, Store_alloc_eq h, typeDisplay?_eq h, displayNameOfId_eq h, displayNameOf_eq h, goTypeNameForMessage_eq h, payloadDynamicTypeNote_eq h, abortRefusal_eq h, methodCarrierKey?_eq h, interfaceDeclaredMethods?_eq h, defaultValue_eq h, allocDecls_eq h, atomicStore_eq h, applyAtomicOp_eq h, applyChanOp_eq h, tyUncomparable_eq h, valueHashability_eq h, checkKeyHashable_eq h, valueEq_eq h, mapEntryIndex?_eq h, mapLookupValue_eq h, commitClause_eq h, applySelectCore_eq h, applySelect_eq h, applySlice_eq h, buildArrayValue_eq h, buildDefaultArrayValue_eq h, mapAssignValue_plan_eq h, applyStmtOpCore_plan_eq h, buildAppendBackingValue_eq h, applyStmtOp_plan_eq h, buildStructFields_eq h, buildStructValue_eq h, convertValueToTy_eq h, indexTargetLoc_eq h, dynamicTypeNameForMessage_eq h, convCapApplyAt_eq h, convCapApply_eq h, syncCell_eq h, applySyncOpCore_eq h, applyTryLock_eq h, applySyncOp_eq h, bindIterVars_eq h, bindParams_eq h, structFieldValue_eq h, promotionHop_eq h, promotionWalk_eq h, receiverAt_eq h, symbolKeyForMessage_eq h, loadResults_eq h, mapIterCandidates_eq h, preprintFatalStop_eq h, panicUnwindStop_eq h, projChainTarget_eq h, resolveChain_eq h, stepUnseqEnter_eq h, unseqGuard_eq h, unseqReadTarget_eq h]

theorem unseqStorePlan_eq_app (h : a.tablesFree = b.tablesFree) (s : Store) (env : LocalEnv) (targets : List (VarId × TargetRef)) (l : List (VarId × VarId)) :
    unseqStorePlan a s env targets l = unseqStorePlan b s env targets l := by
  fun_induction unseqStorePlan a s env targets l <;> (try simp only [types_eq h, typeDisplays_eq h, globals_eq h, structTagCompatible_eq h, loadLoc_eq h, Mem_load_eq h, loadRoot_eq h, Mem_loadBinding_eq h, Mem_loadBindingFor_eq h, Mem_loadElems_eq h, Mem_loadFor_eq h, Mem_loadRun_eq h, Mem_loadSlice_eq h, writeAt_eq h, storeLoc_eq h, Mem_store_eq h, Mem_storeElems_eq h, Mem_storeRun_eq h, normalizeValueForTy_eq h, Store_alloc_eq h, typeDisplay?_eq h, displayNameOfId_eq h, displayNameOf_eq h, goTypeNameForMessage_eq h, payloadDynamicTypeNote_eq h, abortRefusal_eq h, methodCarrierKey?_eq h, interfaceDeclaredMethods?_eq h, defaultValue_eq h, allocDecls_eq h, atomicStore_eq h, applyAtomicOp_eq h, applyChanOp_eq h, tyUncomparable_eq h, valueHashability_eq h, checkKeyHashable_eq h, valueEq_eq h, mapEntryIndex?_eq h, mapLookupValue_eq h, commitClause_eq h, applySelectCore_eq h, applySelect_eq h, applySlice_eq h, buildArrayValue_eq h, buildDefaultArrayValue_eq h, mapAssignValue_plan_eq h, applyStmtOpCore_plan_eq h, buildAppendBackingValue_eq h, applyStmtOp_plan_eq h, buildStructFields_eq h, buildStructValue_eq h, convertValueToTy_eq h, indexTargetLoc_eq h, dynamicTypeNameForMessage_eq h, convCapApplyAt_eq h, convCapApply_eq h, syncCell_eq h, applySyncOpCore_eq h, applyTryLock_eq h, applySyncOp_eq h, bindIterVars_eq h, bindParams_eq h, structFieldValue_eq h, promotionHop_eq h, promotionWalk_eq h, receiverAt_eq h, symbolKeyForMessage_eq h, loadResults_eq h, mapIterCandidates_eq h, preprintFatalStop_eq h, panicUnwindStop_eq h, projChainTarget_eq h, resolveChain_eq h, stepUnseqEnter_eq h, unseqGuard_eq h, unseqReadTarget_eq h, unseqLoad_plan_eq h] at *) <;> simp +zetaDelta only [unseqStorePlan, types_eq h, typeDisplays_eq h, globals_eq h, structTagCompatible_eq h, loadLoc_eq h, Mem_load_eq h, loadRoot_eq h, Mem_loadBinding_eq h, Mem_loadBindingFor_eq h, Mem_loadElems_eq h, Mem_loadFor_eq h, Mem_loadRun_eq h, Mem_loadSlice_eq h, writeAt_eq h, storeLoc_eq h, Mem_store_eq h, Mem_storeElems_eq h, Mem_storeRun_eq h, normalizeValueForTy_eq h, Store_alloc_eq h, typeDisplay?_eq h, displayNameOfId_eq h, displayNameOf_eq h, goTypeNameForMessage_eq h, payloadDynamicTypeNote_eq h, abortRefusal_eq h, methodCarrierKey?_eq h, interfaceDeclaredMethods?_eq h, defaultValue_eq h, allocDecls_eq h, atomicStore_eq h, applyAtomicOp_eq h, applyChanOp_eq h, tyUncomparable_eq h, valueHashability_eq h, checkKeyHashable_eq h, valueEq_eq h, mapEntryIndex?_eq h, mapLookupValue_eq h, commitClause_eq h, applySelectCore_eq h, applySelect_eq h, applySlice_eq h, buildArrayValue_eq h, buildDefaultArrayValue_eq h, mapAssignValue_plan_eq h, applyStmtOpCore_plan_eq h, buildAppendBackingValue_eq h, applyStmtOp_plan_eq h, buildStructFields_eq h, buildStructValue_eq h, convertValueToTy_eq h, indexTargetLoc_eq h, dynamicTypeNameForMessage_eq h, convCapApplyAt_eq h, convCapApply_eq h, syncCell_eq h, applySyncOpCore_eq h, applyTryLock_eq h, applySyncOp_eq h, bindIterVars_eq h, bindParams_eq h, structFieldValue_eq h, promotionHop_eq h, promotionWalk_eq h, receiverAt_eq h, symbolKeyForMessage_eq h, loadResults_eq h, mapIterCandidates_eq h, preprintFatalStop_eq h, panicUnwindStop_eq h, projChainTarget_eq h, resolveChain_eq h, stepUnseqEnter_eq h, unseqGuard_eq h, unseqReadTarget_eq h, unseqLoad_plan_eq h, *]
  all_goals (try (split <;> simp_all))
theorem unseqStorePlan_eq (h : a.tablesFree = b.tablesFree) : @unseqStorePlan a = @unseqStorePlan b := by
  funext s env targets l; exact unseqStorePlan_eq_app h s env targets l

theorem unseqAtom_eq (h : a.tablesFree = b.tablesFree) : @unseqAtom a = @unseqAtom b := by
  delta unseqAtom; simp only [types_eq h, typeDisplays_eq h, globals_eq h, structTagCompatible_eq h, loadLoc_eq h, Mem_load_eq h, loadRoot_eq h, Mem_loadBinding_eq h, Mem_loadBindingFor_eq h, Mem_loadElems_eq h, Mem_loadFor_eq h, Mem_loadRun_eq h, Mem_loadSlice_eq h, writeAt_eq h, storeLoc_eq h, Mem_store_eq h, Mem_storeElems_eq h, Mem_storeRun_eq h, normalizeValueForTy_eq h, Store_alloc_eq h, typeDisplay?_eq h, displayNameOfId_eq h, displayNameOf_eq h, goTypeNameForMessage_eq h, payloadDynamicTypeNote_eq h, abortRefusal_eq h, methodCarrierKey?_eq h, interfaceDeclaredMethods?_eq h, defaultValue_eq h, allocDecls_eq h, atomicStore_eq h, applyAtomicOp_eq h, applyChanOp_eq h, tyUncomparable_eq h, valueHashability_eq h, checkKeyHashable_eq h, valueEq_eq h, mapEntryIndex?_eq h, mapLookupValue_eq h, commitClause_eq h, applySelectCore_eq h, applySelect_eq h, applySlice_eq h, buildArrayValue_eq h, buildDefaultArrayValue_eq h, mapAssignValue_plan_eq h, applyStmtOpCore_plan_eq h, buildAppendBackingValue_eq h, applyStmtOp_plan_eq h, buildStructFields_eq h, buildStructValue_eq h, convertValueToTy_eq h, indexTargetLoc_eq h, dynamicTypeNameForMessage_eq h, convCapApplyAt_eq h, convCapApply_eq h, syncCell_eq h, applySyncOpCore_eq h, applyTryLock_eq h, applySyncOp_eq h, bindIterVars_eq h, bindParams_eq h, structFieldValue_eq h, promotionHop_eq h, promotionWalk_eq h, receiverAt_eq h, symbolKeyForMessage_eq h, loadResults_eq h, mapIterCandidates_eq h, preprintFatalStop_eq h, panicUnwindStop_eq h, projChainTarget_eq h, resolveChain_eq h, stepUnseqEnter_eq h, unseqGuard_eq h, unseqReadTarget_eq h, unseqLoad_plan_eq h, unseqStorePlan_eq h]

theorem unseqAtoms_eq_app (h : a.tablesFree = b.tablesFree) (env : LocalEnv) (s : Store) (es : List Expr) :
    unseqAtoms a env s es = unseqAtoms b env s es := by
  fun_induction unseqAtoms a env s es <;> (try simp only [types_eq h, typeDisplays_eq h, globals_eq h, structTagCompatible_eq h, loadLoc_eq h, Mem_load_eq h, loadRoot_eq h, Mem_loadBinding_eq h, Mem_loadBindingFor_eq h, Mem_loadElems_eq h, Mem_loadFor_eq h, Mem_loadRun_eq h, Mem_loadSlice_eq h, writeAt_eq h, storeLoc_eq h, Mem_store_eq h, Mem_storeElems_eq h, Mem_storeRun_eq h, normalizeValueForTy_eq h, Store_alloc_eq h, typeDisplay?_eq h, displayNameOfId_eq h, displayNameOf_eq h, goTypeNameForMessage_eq h, payloadDynamicTypeNote_eq h, abortRefusal_eq h, methodCarrierKey?_eq h, interfaceDeclaredMethods?_eq h, defaultValue_eq h, allocDecls_eq h, atomicStore_eq h, applyAtomicOp_eq h, applyChanOp_eq h, tyUncomparable_eq h, valueHashability_eq h, checkKeyHashable_eq h, valueEq_eq h, mapEntryIndex?_eq h, mapLookupValue_eq h, commitClause_eq h, applySelectCore_eq h, applySelect_eq h, applySlice_eq h, buildArrayValue_eq h, buildDefaultArrayValue_eq h, mapAssignValue_plan_eq h, applyStmtOpCore_plan_eq h, buildAppendBackingValue_eq h, applyStmtOp_plan_eq h, buildStructFields_eq h, buildStructValue_eq h, convertValueToTy_eq h, indexTargetLoc_eq h, dynamicTypeNameForMessage_eq h, convCapApplyAt_eq h, convCapApply_eq h, syncCell_eq h, applySyncOpCore_eq h, applyTryLock_eq h, applySyncOp_eq h, bindIterVars_eq h, bindParams_eq h, structFieldValue_eq h, promotionHop_eq h, promotionWalk_eq h, receiverAt_eq h, symbolKeyForMessage_eq h, loadResults_eq h, mapIterCandidates_eq h, preprintFatalStop_eq h, panicUnwindStop_eq h, projChainTarget_eq h, resolveChain_eq h, stepUnseqEnter_eq h, unseqGuard_eq h, unseqReadTarget_eq h, unseqLoad_plan_eq h, unseqStorePlan_eq h, unseqAtom_eq h] at *) <;> simp +zetaDelta only [unseqAtoms, types_eq h, typeDisplays_eq h, globals_eq h, structTagCompatible_eq h, loadLoc_eq h, Mem_load_eq h, loadRoot_eq h, Mem_loadBinding_eq h, Mem_loadBindingFor_eq h, Mem_loadElems_eq h, Mem_loadFor_eq h, Mem_loadRun_eq h, Mem_loadSlice_eq h, writeAt_eq h, storeLoc_eq h, Mem_store_eq h, Mem_storeElems_eq h, Mem_storeRun_eq h, normalizeValueForTy_eq h, Store_alloc_eq h, typeDisplay?_eq h, displayNameOfId_eq h, displayNameOf_eq h, goTypeNameForMessage_eq h, payloadDynamicTypeNote_eq h, abortRefusal_eq h, methodCarrierKey?_eq h, interfaceDeclaredMethods?_eq h, defaultValue_eq h, allocDecls_eq h, atomicStore_eq h, applyAtomicOp_eq h, applyChanOp_eq h, tyUncomparable_eq h, valueHashability_eq h, checkKeyHashable_eq h, valueEq_eq h, mapEntryIndex?_eq h, mapLookupValue_eq h, commitClause_eq h, applySelectCore_eq h, applySelect_eq h, applySlice_eq h, buildArrayValue_eq h, buildDefaultArrayValue_eq h, mapAssignValue_plan_eq h, applyStmtOpCore_plan_eq h, buildAppendBackingValue_eq h, applyStmtOp_plan_eq h, buildStructFields_eq h, buildStructValue_eq h, convertValueToTy_eq h, indexTargetLoc_eq h, dynamicTypeNameForMessage_eq h, convCapApplyAt_eq h, convCapApply_eq h, syncCell_eq h, applySyncOpCore_eq h, applyTryLock_eq h, applySyncOp_eq h, bindIterVars_eq h, bindParams_eq h, structFieldValue_eq h, promotionHop_eq h, promotionWalk_eq h, receiverAt_eq h, symbolKeyForMessage_eq h, loadResults_eq h, mapIterCandidates_eq h, preprintFatalStop_eq h, panicUnwindStop_eq h, projChainTarget_eq h, resolveChain_eq h, stepUnseqEnter_eq h, unseqGuard_eq h, unseqReadTarget_eq h, unseqLoad_plan_eq h, unseqStorePlan_eq h, unseqAtom_eq h, *]
  all_goals (try (split <;> simp_all))
theorem unseqAtoms_eq (h : a.tablesFree = b.tablesFree) : @unseqAtoms a = @unseqAtoms b := by
  funext env s es; exact unseqAtoms_eq_app h env s es

theorem unseqUnfrozenAnchor?_eq_app (h : a.tablesFree = b.tablesFree) (s : Store) (v : GoValue) (steps : List TargetStep) (idxs : List GoValue) :
    unseqUnfrozenAnchor? a s v steps idxs = unseqUnfrozenAnchor? b s v steps idxs := by
  fun_induction unseqUnfrozenAnchor? a s v steps idxs <;> (try simp only [types_eq h, typeDisplays_eq h, globals_eq h, structTagCompatible_eq h, loadLoc_eq h, Mem_load_eq h, loadRoot_eq h, Mem_loadBinding_eq h, Mem_loadBindingFor_eq h, Mem_loadElems_eq h, Mem_loadFor_eq h, Mem_loadRun_eq h, Mem_loadSlice_eq h, writeAt_eq h, storeLoc_eq h, Mem_store_eq h, Mem_storeElems_eq h, Mem_storeRun_eq h, normalizeValueForTy_eq h, Store_alloc_eq h, typeDisplay?_eq h, displayNameOfId_eq h, displayNameOf_eq h, goTypeNameForMessage_eq h, payloadDynamicTypeNote_eq h, abortRefusal_eq h, methodCarrierKey?_eq h, interfaceDeclaredMethods?_eq h, defaultValue_eq h, allocDecls_eq h, atomicStore_eq h, applyAtomicOp_eq h, applyChanOp_eq h, tyUncomparable_eq h, valueHashability_eq h, checkKeyHashable_eq h, valueEq_eq h, mapEntryIndex?_eq h, mapLookupValue_eq h, commitClause_eq h, applySelectCore_eq h, applySelect_eq h, applySlice_eq h, buildArrayValue_eq h, buildDefaultArrayValue_eq h, mapAssignValue_plan_eq h, applyStmtOpCore_plan_eq h, buildAppendBackingValue_eq h, applyStmtOp_plan_eq h, buildStructFields_eq h, buildStructValue_eq h, convertValueToTy_eq h, indexTargetLoc_eq h, dynamicTypeNameForMessage_eq h, convCapApplyAt_eq h, convCapApply_eq h, syncCell_eq h, applySyncOpCore_eq h, applyTryLock_eq h, applySyncOp_eq h, bindIterVars_eq h, bindParams_eq h, structFieldValue_eq h, promotionHop_eq h, promotionWalk_eq h, receiverAt_eq h, symbolKeyForMessage_eq h, loadResults_eq h, mapIterCandidates_eq h, preprintFatalStop_eq h, panicUnwindStop_eq h, projChainTarget_eq h, resolveChain_eq h, stepUnseqEnter_eq h, unseqGuard_eq h, unseqReadTarget_eq h, unseqLoad_plan_eq h, unseqStorePlan_eq h, unseqAtom_eq h, unseqAtoms_eq h] at *) <;> simp +zetaDelta only [unseqUnfrozenAnchor?, types_eq h, typeDisplays_eq h, globals_eq h, structTagCompatible_eq h, loadLoc_eq h, Mem_load_eq h, loadRoot_eq h, Mem_loadBinding_eq h, Mem_loadBindingFor_eq h, Mem_loadElems_eq h, Mem_loadFor_eq h, Mem_loadRun_eq h, Mem_loadSlice_eq h, writeAt_eq h, storeLoc_eq h, Mem_store_eq h, Mem_storeElems_eq h, Mem_storeRun_eq h, normalizeValueForTy_eq h, Store_alloc_eq h, typeDisplay?_eq h, displayNameOfId_eq h, displayNameOf_eq h, goTypeNameForMessage_eq h, payloadDynamicTypeNote_eq h, abortRefusal_eq h, methodCarrierKey?_eq h, interfaceDeclaredMethods?_eq h, defaultValue_eq h, allocDecls_eq h, atomicStore_eq h, applyAtomicOp_eq h, applyChanOp_eq h, tyUncomparable_eq h, valueHashability_eq h, checkKeyHashable_eq h, valueEq_eq h, mapEntryIndex?_eq h, mapLookupValue_eq h, commitClause_eq h, applySelectCore_eq h, applySelect_eq h, applySlice_eq h, buildArrayValue_eq h, buildDefaultArrayValue_eq h, mapAssignValue_plan_eq h, applyStmtOpCore_plan_eq h, buildAppendBackingValue_eq h, applyStmtOp_plan_eq h, buildStructFields_eq h, buildStructValue_eq h, convertValueToTy_eq h, indexTargetLoc_eq h, dynamicTypeNameForMessage_eq h, convCapApplyAt_eq h, convCapApply_eq h, syncCell_eq h, applySyncOpCore_eq h, applyTryLock_eq h, applySyncOp_eq h, bindIterVars_eq h, bindParams_eq h, structFieldValue_eq h, promotionHop_eq h, promotionWalk_eq h, receiverAt_eq h, symbolKeyForMessage_eq h, loadResults_eq h, mapIterCandidates_eq h, preprintFatalStop_eq h, panicUnwindStop_eq h, projChainTarget_eq h, resolveChain_eq h, stepUnseqEnter_eq h, unseqGuard_eq h, unseqReadTarget_eq h, unseqLoad_plan_eq h, unseqStorePlan_eq h, unseqAtom_eq h, unseqAtoms_eq h, *]
  all_goals (try (split <;> simp_all))
theorem unseqUnfrozenAnchor?_eq (h : a.tablesFree = b.tablesFree) : @unseqUnfrozenAnchor? a = @unseqUnfrozenAnchor? b := by
  funext s v steps idxs; exact unseqUnfrozenAnchor?_eq_app h s v steps idxs

theorem unseqUnfrozenPlan?_eq (h : a.tablesFree = b.tablesFree) : @unseqUnfrozenPlan? a = @unseqUnfrozenPlan? b := by
  delta unseqUnfrozenPlan?; simp only [types_eq h, typeDisplays_eq h, globals_eq h, structTagCompatible_eq h, loadLoc_eq h, Mem_load_eq h, loadRoot_eq h, Mem_loadBinding_eq h, Mem_loadBindingFor_eq h, Mem_loadElems_eq h, Mem_loadFor_eq h, Mem_loadRun_eq h, Mem_loadSlice_eq h, writeAt_eq h, storeLoc_eq h, Mem_store_eq h, Mem_storeElems_eq h, Mem_storeRun_eq h, normalizeValueForTy_eq h, Store_alloc_eq h, typeDisplay?_eq h, displayNameOfId_eq h, displayNameOf_eq h, goTypeNameForMessage_eq h, payloadDynamicTypeNote_eq h, abortRefusal_eq h, methodCarrierKey?_eq h, interfaceDeclaredMethods?_eq h, defaultValue_eq h, allocDecls_eq h, atomicStore_eq h, applyAtomicOp_eq h, applyChanOp_eq h, tyUncomparable_eq h, valueHashability_eq h, checkKeyHashable_eq h, valueEq_eq h, mapEntryIndex?_eq h, mapLookupValue_eq h, commitClause_eq h, applySelectCore_eq h, applySelect_eq h, applySlice_eq h, buildArrayValue_eq h, buildDefaultArrayValue_eq h, mapAssignValue_plan_eq h, applyStmtOpCore_plan_eq h, buildAppendBackingValue_eq h, applyStmtOp_plan_eq h, buildStructFields_eq h, buildStructValue_eq h, convertValueToTy_eq h, indexTargetLoc_eq h, dynamicTypeNameForMessage_eq h, convCapApplyAt_eq h, convCapApply_eq h, syncCell_eq h, applySyncOpCore_eq h, applyTryLock_eq h, applySyncOp_eq h, bindIterVars_eq h, bindParams_eq h, structFieldValue_eq h, promotionHop_eq h, promotionWalk_eq h, receiverAt_eq h, symbolKeyForMessage_eq h, loadResults_eq h, mapIterCandidates_eq h, preprintFatalStop_eq h, panicUnwindStop_eq h, projChainTarget_eq h, resolveChain_eq h, stepUnseqEnter_eq h, unseqGuard_eq h, unseqReadTarget_eq h, unseqLoad_plan_eq h, unseqStorePlan_eq h, unseqAtom_eq h, unseqAtoms_eq h, unseqUnfrozenAnchor?_eq h]

theorem unseqTargetPlan_eq (h : a.tablesFree = b.tablesFree) : @unseqTargetPlan a = @unseqTargetPlan b := by
  delta unseqTargetPlan; simp only [types_eq h, typeDisplays_eq h, globals_eq h, structTagCompatible_eq h, loadLoc_eq h, Mem_load_eq h, loadRoot_eq h, Mem_loadBinding_eq h, Mem_loadBindingFor_eq h, Mem_loadElems_eq h, Mem_loadFor_eq h, Mem_loadRun_eq h, Mem_loadSlice_eq h, writeAt_eq h, storeLoc_eq h, Mem_store_eq h, Mem_storeElems_eq h, Mem_storeRun_eq h, normalizeValueForTy_eq h, Store_alloc_eq h, typeDisplay?_eq h, displayNameOfId_eq h, displayNameOf_eq h, goTypeNameForMessage_eq h, payloadDynamicTypeNote_eq h, abortRefusal_eq h, methodCarrierKey?_eq h, interfaceDeclaredMethods?_eq h, defaultValue_eq h, allocDecls_eq h, atomicStore_eq h, applyAtomicOp_eq h, applyChanOp_eq h, tyUncomparable_eq h, valueHashability_eq h, checkKeyHashable_eq h, valueEq_eq h, mapEntryIndex?_eq h, mapLookupValue_eq h, commitClause_eq h, applySelectCore_eq h, applySelect_eq h, applySlice_eq h, buildArrayValue_eq h, buildDefaultArrayValue_eq h, mapAssignValue_plan_eq h, applyStmtOpCore_plan_eq h, buildAppendBackingValue_eq h, applyStmtOp_plan_eq h, buildStructFields_eq h, buildStructValue_eq h, convertValueToTy_eq h, indexTargetLoc_eq h, dynamicTypeNameForMessage_eq h, convCapApplyAt_eq h, convCapApply_eq h, syncCell_eq h, applySyncOpCore_eq h, applyTryLock_eq h, applySyncOp_eq h, bindIterVars_eq h, bindParams_eq h, structFieldValue_eq h, promotionHop_eq h, promotionWalk_eq h, receiverAt_eq h, symbolKeyForMessage_eq h, loadResults_eq h, mapIterCandidates_eq h, preprintFatalStop_eq h, panicUnwindStop_eq h, projChainTarget_eq h, resolveChain_eq h, stepUnseqEnter_eq h, unseqGuard_eq h, unseqReadTarget_eq h, unseqLoad_plan_eq h, unseqStorePlan_eq h, unseqAtom_eq h, unseqAtoms_eq h, unseqUnfrozenAnchor?_eq h, unseqUnfrozenPlan?_eq h]

theorem stepUnseqNext_eq (h : a.tablesFree = b.tablesFree) : @stepUnseqNext a = @stepUnseqNext b := by
  delta stepUnseqNext; simp only [types_eq h, typeDisplays_eq h, globals_eq h, structTagCompatible_eq h, loadLoc_eq h, Mem_load_eq h, loadRoot_eq h, Mem_loadBinding_eq h, Mem_loadBindingFor_eq h, Mem_loadElems_eq h, Mem_loadFor_eq h, Mem_loadRun_eq h, Mem_loadSlice_eq h, writeAt_eq h, storeLoc_eq h, Mem_store_eq h, Mem_storeElems_eq h, Mem_storeRun_eq h, normalizeValueForTy_eq h, Store_alloc_eq h, typeDisplay?_eq h, displayNameOfId_eq h, displayNameOf_eq h, goTypeNameForMessage_eq h, payloadDynamicTypeNote_eq h, abortRefusal_eq h, methodCarrierKey?_eq h, interfaceDeclaredMethods?_eq h, defaultValue_eq h, allocDecls_eq h, atomicStore_eq h, applyAtomicOp_eq h, applyChanOp_eq h, tyUncomparable_eq h, valueHashability_eq h, checkKeyHashable_eq h, valueEq_eq h, mapEntryIndex?_eq h, mapLookupValue_eq h, commitClause_eq h, applySelectCore_eq h, applySelect_eq h, applySlice_eq h, buildArrayValue_eq h, buildDefaultArrayValue_eq h, mapAssignValue_plan_eq h, applyStmtOpCore_plan_eq h, buildAppendBackingValue_eq h, applyStmtOp_plan_eq h, buildStructFields_eq h, buildStructValue_eq h, convertValueToTy_eq h, indexTargetLoc_eq h, dynamicTypeNameForMessage_eq h, convCapApplyAt_eq h, convCapApply_eq h, syncCell_eq h, applySyncOpCore_eq h, applyTryLock_eq h, applySyncOp_eq h, bindIterVars_eq h, bindParams_eq h, structFieldValue_eq h, promotionHop_eq h, promotionWalk_eq h, receiverAt_eq h, symbolKeyForMessage_eq h, loadResults_eq h, mapIterCandidates_eq h, preprintFatalStop_eq h, panicUnwindStop_eq h, projChainTarget_eq h, resolveChain_eq h, stepUnseqEnter_eq h, unseqGuard_eq h, unseqReadTarget_eq h, unseqLoad_plan_eq h, unseqStorePlan_eq h, unseqAtom_eq h, unseqAtoms_eq h, unseqUnfrozenAnchor?_eq h, unseqUnfrozenPlan?_eq h, unseqTargetPlan_eq h]

theorem stepUnseqValue_eq (h : a.tablesFree = b.tablesFree) : @stepUnseqValue a = @stepUnseqValue b := by
  delta stepUnseqValue; simp only [types_eq h, typeDisplays_eq h, globals_eq h, structTagCompatible_eq h, loadLoc_eq h, Mem_load_eq h, loadRoot_eq h, Mem_loadBinding_eq h, Mem_loadBindingFor_eq h, Mem_loadElems_eq h, Mem_loadFor_eq h, Mem_loadRun_eq h, Mem_loadSlice_eq h, writeAt_eq h, storeLoc_eq h, Mem_store_eq h, Mem_storeElems_eq h, Mem_storeRun_eq h, normalizeValueForTy_eq h, Store_alloc_eq h, typeDisplay?_eq h, displayNameOfId_eq h, displayNameOf_eq h, goTypeNameForMessage_eq h, payloadDynamicTypeNote_eq h, abortRefusal_eq h, methodCarrierKey?_eq h, interfaceDeclaredMethods?_eq h, defaultValue_eq h, allocDecls_eq h, atomicStore_eq h, applyAtomicOp_eq h, applyChanOp_eq h, tyUncomparable_eq h, valueHashability_eq h, checkKeyHashable_eq h, valueEq_eq h, mapEntryIndex?_eq h, mapLookupValue_eq h, commitClause_eq h, applySelectCore_eq h, applySelect_eq h, applySlice_eq h, buildArrayValue_eq h, buildDefaultArrayValue_eq h, mapAssignValue_plan_eq h, applyStmtOpCore_plan_eq h, buildAppendBackingValue_eq h, applyStmtOp_plan_eq h, buildStructFields_eq h, buildStructValue_eq h, convertValueToTy_eq h, indexTargetLoc_eq h, dynamicTypeNameForMessage_eq h, convCapApplyAt_eq h, convCapApply_eq h, syncCell_eq h, applySyncOpCore_eq h, applyTryLock_eq h, applySyncOp_eq h, bindIterVars_eq h, bindParams_eq h, structFieldValue_eq h, promotionHop_eq h, promotionWalk_eq h, receiverAt_eq h, symbolKeyForMessage_eq h, loadResults_eq h, mapIterCandidates_eq h, preprintFatalStop_eq h, panicUnwindStop_eq h, projChainTarget_eq h, resolveChain_eq h, stepUnseqEnter_eq h, unseqGuard_eq h, unseqReadTarget_eq h, unseqLoad_plan_eq h, unseqStorePlan_eq h, unseqAtom_eq h, unseqAtoms_eq h, unseqUnfrozenAnchor?_eq h, unseqUnfrozenPlan?_eq h, unseqTargetPlan_eq h, stepUnseqNext_eq h]

theorem storeTarget_plan_eq (h : a.tablesFree = b.tablesFree) : @storeTarget.plan a = @storeTarget.plan b := by
  delta storeTarget.plan; simp only [types_eq h, typeDisplays_eq h, globals_eq h, structTagCompatible_eq h, loadLoc_eq h, Mem_load_eq h, loadRoot_eq h, Mem_loadBinding_eq h, Mem_loadBindingFor_eq h, Mem_loadElems_eq h, Mem_loadFor_eq h, Mem_loadRun_eq h, Mem_loadSlice_eq h, writeAt_eq h, storeLoc_eq h, Mem_store_eq h, Mem_storeElems_eq h, Mem_storeRun_eq h, normalizeValueForTy_eq h, Store_alloc_eq h, typeDisplay?_eq h, displayNameOfId_eq h, displayNameOf_eq h, goTypeNameForMessage_eq h, payloadDynamicTypeNote_eq h, abortRefusal_eq h, methodCarrierKey?_eq h, interfaceDeclaredMethods?_eq h, defaultValue_eq h, allocDecls_eq h, atomicStore_eq h, applyAtomicOp_eq h, applyChanOp_eq h, tyUncomparable_eq h, valueHashability_eq h, checkKeyHashable_eq h, valueEq_eq h, mapEntryIndex?_eq h, mapLookupValue_eq h, commitClause_eq h, applySelectCore_eq h, applySelect_eq h, applySlice_eq h, buildArrayValue_eq h, buildDefaultArrayValue_eq h, mapAssignValue_plan_eq h, applyStmtOpCore_plan_eq h, buildAppendBackingValue_eq h, applyStmtOp_plan_eq h, buildStructFields_eq h, buildStructValue_eq h, convertValueToTy_eq h, indexTargetLoc_eq h, dynamicTypeNameForMessage_eq h, convCapApplyAt_eq h, convCapApply_eq h, syncCell_eq h, applySyncOpCore_eq h, applyTryLock_eq h, applySyncOp_eq h, bindIterVars_eq h, bindParams_eq h, structFieldValue_eq h, promotionHop_eq h, promotionWalk_eq h, receiverAt_eq h, symbolKeyForMessage_eq h, loadResults_eq h, mapIterCandidates_eq h, preprintFatalStop_eq h, panicUnwindStop_eq h, projChainTarget_eq h, resolveChain_eq h, stepUnseqEnter_eq h, unseqGuard_eq h, unseqReadTarget_eq h, unseqLoad_plan_eq h, unseqStorePlan_eq h, unseqAtom_eq h, unseqAtoms_eq h, unseqUnfrozenAnchor?_eq h, unseqUnfrozenPlan?_eq h, unseqTargetPlan_eq h, stepUnseqNext_eq h, stepUnseqValue_eq h]

end TableMono
/-! ## §4 The table readers

§4a: the readers whose answer a RECORD certifies. Each either reads the method-set record of the
carrier it answers about — refusing without it — or makes positive lookups only; so wherever the
slice did not refuse, its answer is the whole's. Two statement shapes: `_eq_of_recorded`, an
equality under the slice's record (`methodDecl?`, `promotion?`, `resolveMethod?`, the signatures,
satisfaction of a requirement, the preprint members), and `_eq` under `Passes` — the reader's
answer under the slice is a value or a Go panic, what `toResult` lets a successful step carry —
for the composed readers (`firstUnsatisfiedMethod?`, `typeAssertValue`, `typePkgForMessage`,
`typeAssertPanicMessage`, `applyStrictOp`, `applyStrictOpPick`, `applyRhsOp`); `_mono` for the
`Option`/`Except` readers of the abort phase (`phaseMark`, the renderers, `abortMsg`,
`stepPanicStop`). §4b: the frame-entry family, which only PRESERVES a success — a slice refuses
where the whole dispatches (`callee?`, `promotedCallee`, `dynamicDispatch?`, `enterFrame.plan`,
`enterFramePickV`, and the two step helpers that enter frames). -/

set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false

/-- Rewrite every table-free helper (§3) from the slice to the whole, given the `tablesFree`
equality. -/
macro "free_rw" hf:term : tactic => `(tactic| simp only [TableMono.types_eq $hf, TableMono.typeDisplays_eq $hf, TableMono.globals_eq $hf, TableMono.structTagCompatible_eq $hf, TableMono.loadLoc_eq $hf, TableMono.Mem_load_eq $hf, TableMono.loadRoot_eq $hf, TableMono.Mem_loadBinding_eq $hf, TableMono.Mem_loadBindingFor_eq $hf, TableMono.Mem_loadElems_eq $hf, TableMono.Mem_loadFor_eq $hf, TableMono.Mem_loadRun_eq $hf, TableMono.Mem_loadSlice_eq $hf, TableMono.writeAt_eq $hf, TableMono.storeLoc_eq $hf, TableMono.Mem_store_eq $hf, TableMono.Mem_storeElems_eq $hf, TableMono.Mem_storeRun_eq $hf, TableMono.normalizeValueForTy_eq $hf, TableMono.Store_alloc_eq $hf, TableMono.typeDisplay?_eq $hf, TableMono.displayNameOfId_eq $hf, TableMono.displayNameOf_eq $hf, TableMono.goTypeNameForMessage_eq $hf, TableMono.payloadDynamicTypeNote_eq $hf, TableMono.abortRefusal_eq $hf, TableMono.methodCarrierKey?_eq $hf, TableMono.interfaceDeclaredMethods?_eq $hf, TableMono.defaultValue_eq $hf, TableMono.allocDecls_eq $hf, TableMono.atomicStore_eq $hf, TableMono.applyAtomicOp_eq $hf, TableMono.applyChanOp_eq $hf, TableMono.tyUncomparable_eq $hf, TableMono.valueHashability_eq $hf, TableMono.checkKeyHashable_eq $hf, TableMono.valueEq_eq $hf, TableMono.mapEntryIndex?_eq $hf, TableMono.mapLookupValue_eq $hf, TableMono.commitClause_eq $hf, TableMono.applySelectCore_eq $hf, TableMono.applySelect_eq $hf, TableMono.applySlice_eq $hf, TableMono.buildArrayValue_eq $hf, TableMono.buildDefaultArrayValue_eq $hf, TableMono.mapAssignValue_plan_eq $hf, TableMono.applyStmtOpCore_plan_eq $hf, TableMono.buildAppendBackingValue_eq $hf, TableMono.applyStmtOp_plan_eq $hf, TableMono.buildStructFields_eq $hf, TableMono.buildStructValue_eq $hf, TableMono.convertValueToTy_eq $hf, TableMono.indexTargetLoc_eq $hf, TableMono.dynamicTypeNameForMessage_eq $hf, TableMono.convCapApplyAt_eq $hf, TableMono.convCapApply_eq $hf, TableMono.syncCell_eq $hf, TableMono.applySyncOpCore_eq $hf, TableMono.applyTryLock_eq $hf, TableMono.applySyncOp_eq $hf, TableMono.bindIterVars_eq $hf, TableMono.bindParams_eq $hf, TableMono.structFieldValue_eq $hf, TableMono.promotionHop_eq $hf, TableMono.promotionWalk_eq $hf, TableMono.receiverAt_eq $hf, TableMono.symbolKeyForMessage_eq $hf, TableMono.loadResults_eq $hf, TableMono.mapIterCandidates_eq $hf, TableMono.preprintFatalStop_eq $hf, TableMono.panicUnwindStop_eq $hf, TableMono.projChainTarget_eq $hf, TableMono.resolveChain_eq $hf, TableMono.stepUnseqEnter_eq $hf, TableMono.unseqGuard_eq $hf, TableMono.unseqReadTarget_eq $hf, TableMono.unseqLoad_plan_eq $hf, TableMono.unseqStorePlan_eq $hf, TableMono.unseqAtom_eq $hf, TableMono.unseqAtoms_eq $hf, TableMono.unseqUnfrozenAnchor?_eq $hf, TableMono.unseqUnfrozenPlan?_eq $hf, TableMono.unseqTargetPlan_eq $hf, TableMono.stepUnseqNext_eq $hf, TableMono.stepUnseqValue_eq $hf, TableMono.storeTarget_plan_eq $hf])

namespace TableMono
theorem foldl_ext' {α β : Type} {l : List α} {f g : β → α → β}
    (hfg : ∀ acc x, x ∈ l → f acc x = g acc x) (init : β) : l.foldl f init = l.foldl g init := by
  induction l generalizing init with
  | nil => rfl
  | cons x xs ih =>
    rw [List.foldl_cons, List.foldl_cons, hfg init x (List.mem_cons_self ..)]
    exact ih (fun acc y hy => hfg acc y (List.mem_cons_of_mem _ hy)) _
end TableMono
macro "free_rw_at" hf:term:max loc:ident : tactic => `(tactic| simp only [TableMono.types_eq $hf, TableMono.typeDisplays_eq $hf, TableMono.globals_eq $hf, TableMono.structTagCompatible_eq $hf, TableMono.loadLoc_eq $hf, TableMono.Mem_load_eq $hf, TableMono.loadRoot_eq $hf, TableMono.Mem_loadBinding_eq $hf, TableMono.Mem_loadBindingFor_eq $hf, TableMono.Mem_loadElems_eq $hf, TableMono.Mem_loadFor_eq $hf, TableMono.Mem_loadRun_eq $hf, TableMono.Mem_loadSlice_eq $hf, TableMono.writeAt_eq $hf, TableMono.storeLoc_eq $hf, TableMono.Mem_store_eq $hf, TableMono.Mem_storeElems_eq $hf, TableMono.Mem_storeRun_eq $hf, TableMono.normalizeValueForTy_eq $hf, TableMono.Store_alloc_eq $hf, TableMono.typeDisplay?_eq $hf, TableMono.displayNameOfId_eq $hf, TableMono.displayNameOf_eq $hf, TableMono.goTypeNameForMessage_eq $hf, TableMono.payloadDynamicTypeNote_eq $hf, TableMono.abortRefusal_eq $hf, TableMono.methodCarrierKey?_eq $hf, TableMono.interfaceDeclaredMethods?_eq $hf, TableMono.defaultValue_eq $hf, TableMono.allocDecls_eq $hf, TableMono.atomicStore_eq $hf, TableMono.applyAtomicOp_eq $hf, TableMono.applyChanOp_eq $hf, TableMono.tyUncomparable_eq $hf, TableMono.valueHashability_eq $hf, TableMono.checkKeyHashable_eq $hf, TableMono.valueEq_eq $hf, TableMono.mapEntryIndex?_eq $hf, TableMono.mapLookupValue_eq $hf, TableMono.commitClause_eq $hf, TableMono.applySelectCore_eq $hf, TableMono.applySelect_eq $hf, TableMono.applySlice_eq $hf, TableMono.buildArrayValue_eq $hf, TableMono.buildDefaultArrayValue_eq $hf, TableMono.mapAssignValue_plan_eq $hf, TableMono.applyStmtOpCore_plan_eq $hf, TableMono.buildAppendBackingValue_eq $hf, TableMono.applyStmtOp_plan_eq $hf, TableMono.buildStructFields_eq $hf, TableMono.buildStructValue_eq $hf, TableMono.convertValueToTy_eq $hf, TableMono.indexTargetLoc_eq $hf, TableMono.dynamicTypeNameForMessage_eq $hf, TableMono.convCapApplyAt_eq $hf, TableMono.convCapApply_eq $hf, TableMono.syncCell_eq $hf, TableMono.applySyncOpCore_eq $hf, TableMono.applyTryLock_eq $hf, TableMono.applySyncOp_eq $hf, TableMono.bindIterVars_eq $hf, TableMono.bindParams_eq $hf, TableMono.structFieldValue_eq $hf, TableMono.promotionHop_eq $hf, TableMono.promotionWalk_eq $hf, TableMono.receiverAt_eq $hf, TableMono.symbolKeyForMessage_eq $hf, TableMono.loadResults_eq $hf, TableMono.mapIterCandidates_eq $hf, TableMono.preprintFatalStop_eq $hf, TableMono.panicUnwindStop_eq $hf, TableMono.projChainTarget_eq $hf, TableMono.resolveChain_eq $hf, TableMono.stepUnseqEnter_eq $hf, TableMono.unseqGuard_eq $hf, TableMono.unseqReadTarget_eq $hf, TableMono.unseqLoad_plan_eq $hf, TableMono.unseqStorePlan_eq $hf, TableMono.unseqAtom_eq $hf, TableMono.unseqAtoms_eq $hf, TableMono.unseqUnfrozenAnchor?_eq $hf, TableMono.unseqUnfrozenPlan?_eq $hf, TableMono.unseqTargetPlan_eq $hf, TableMono.stepUnseqNext_eq $hf, TableMono.stepUnseqValue_eq $hf, TableMono.storeTarget_plan_eq $hf] at $loc:ident)

namespace ProgramCtx.SubTables
variable {a b : ProgramCtx}

/-! ### §4b The frame-entry family: a success is preserved -/

/-- A kept `Func` keeps its `MethodInfo` (closure), so the dispatch table answers the same for it. -/
theorem methodInfoByFuncId?_eq_of_func (h : a.SubTables b) {f : Func}
    (hf : f ∈ a.functions.toList) : methodInfoByFuncId? a f.id = methodInfoByFuncId? b f.id := by
  cases hb : methodInfoByFuncId? b f.id with
  | none =>
    cases ha : methodInfoByFuncId? a f.id with
    | none => rfl
    | some m => have := h.methodInfoByFuncId?_mono ha; rw [hb] at this; cases this
  | some m =>
    obtain ⟨hid, hmb⟩ := methodInfoByFuncId?_some hb
    have hma : m ∈ a.methods.toList := h.closed.methodOfFunc m hmb ⟨f, hf, hid.symm⟩
    have hp : (m.funcId == f.id) = true := by
      rw [methodInfoByFuncId?_eq_find?] at hb; have := List.find?_some hb; exact this
    obtain ⟨m', hm'⟩ : ∃ m', methodInfoByFuncId? a f.id = some m' := by
      rw [methodInfoByFuncId?_eq_find?]
      cases hfa : a.methods.toList.find? (fun method => method.funcId == f.id) with
      | some m' => exact ⟨m', rfl⟩
      | none => exact absurd hp (List.find?_eq_none.mp hfa m hma)
    have := h.methodInfoByFuncId?_mono hm'
    rw [hb] at this
    rw [hm']; exact this.symm

theorem callee?_mono (h : a.SubTables b) {fid : FuncId} {c : Callee} (hc : callee? a fid = some c) :
    callee? b fid = some c := by
  unfold callee? at hc ⊢
  cases hfa : findFunctionIn? a.functions fid with
  | some f => rw [hfa] at hc; rw [h.findFunctionIn?_mono hfa]; exact hc
  | none =>
    rw [hfa] at hc
    cases hpa : a.promotions.find? (fun p => methodFuncId p.type.key p.member == fid) with
    | none => rw [hpa] at hc; cases hc
    | some p =>
      rw [hpa] at hc
      have hpb : p ∈ b.promotions.toList :=
        h.mem_promotions (by simpa using Array.mem_of_find?_eq_some hpa)
      have hp := Array.find?_some hpa
      have hid : methodFuncId p.type.key p.member = fid := FuncId.beq_sound hp
      have hnf : findFunctionIn? b.functions fid = none := by
        rw [← hid]; exact h.keyed.promotionNoFunc p hpb
      rw [hnf]
      have hpl : a.promotions.toList.find? (fun p => methodFuncId p.type.key p.member == fid) = some p := by
        rw [Array.find?_toList]; exact hpa
      have hpb' := find?_sublist_mono h.promotions hpl (fun y hy hpy =>
        nodup_map_inj h.keyed.promotionIds hy hpb ((FuncId.beq_sound hpy).trans hid.symm))
      rw [Array.find?_toList] at hpb'
      rw [hpb']; exact hc

/-- Inverting the promoted arm: a record answered, for a defined base, with the record's own
resolution. -/
theorem resolvePromoted?_inv {ctx : ProgramCtx} {base : Ty} {ptr : Bool} {M : Declaration.MemberId}
    {r : MethodResolution} (hp : resolvePromoted? ctx base ptr M = some r) :
    ∃ idx carrier p, base = .defined idx ∧ ctx.types.nameOf? idx = some carrier ∧
      promotion? ctx carrier M = some p ∧ (p.inPtrSetOnly && !ptr) = false ∧ r = .ofPromotion p := by
  unfold resolvePromoted? at hp
  split at hp
  · rename_i idx
    split at hp
    · rename_i carrier hn
      split at hp
      · rename_i p hpp
        split at hp
        · cases hp
        · rename_i hset
          cases hp
          exact ⟨idx, carrier, p, rfl, hn, hpp, by simpa using hset, rfl⟩
      · cases hp
    · cases hp
  · cases hp

theorem resolveMethod?_mono (h : a.SubTables b) {t : Ty} {M : Declaration.MemberId}
    {r : MethodResolution} (hr : resolveMethod? a t M = some r) : resolveMethod? b t M = some r := by
  have hty := types_eq h.tablesFree_eq
  -- a found promotion record: its carrier declares nothing for the member in the whole
  have hrec : ∀ {idx carrier p}, a.types.nameOf? idx = some carrier → promotion? a carrier M = some p →
      promotion? b carrier M = some p ∧ b.types.nameOf? idx = some carrier ∧
        methodDecl? b (.defined idx) M = none ∧ methodDecl? b (.pointer (.defined idx)) M = none := by
    intro idx carrier p hn hp
    obtain ⟨hc, hm, hpa⟩ := promotion?_some hp
    have hpb : p ∈ b.promotions.toList := h.mem_promotions (by simpa using hpa)
    have hn' : b.types.nameOf? idx = some carrier := hty ▸ hn
    have hnd := h.keyed.promotionNoDecl p hpb idx (hc ▸ hn')
    rw [MemberId.beq_sound hm] at hnd
    exact ⟨h.promotion?_mono hp, hn', hnd.1, hnd.2⟩
  unfold resolveMethod? at hr
  split at hr
  · rename_i info hd
    cases hr
    exact resolveMethod?_declared (h.methodDecl?_mono hd)
  · rename_i hd
    split at hr
    · cases hr
    · cases hr
    · rename_i elem hne1 hne2
      split at hr
      · rename_i info hde
        cases hr
        obtain ⟨hid, hrecv, hmem⟩ := methodDecl?_some' hde
        have hnone : methodDecl? b (.pointer elem) M = none := by
          have := h.keyed.noPtrTwin info (h.mem_methods hmem) elem hrecv
          rwa [hid] at this
        exact resolveMethod?_ptrDeclared hnone hne1 hne2 (h.methodDecl?_mono hde)
      · obtain ⟨idx, carrier, p, rfl, hn, hp, -, rfl⟩ := resolvePromoted?_inv hr
        obtain ⟨hpb, hn', hnd1, hnd2⟩ := hrec hn hp
        exact resolveMethod?_promotedPtr hnd2 hnd1 hn' hpb
    · obtain ⟨idx, carrier, p, rfl, hn, hp, hset, rfl⟩ := resolvePromoted?_inv hr
      obtain ⟨hpb, hn', hnd1, -⟩ := hrec hn hp
      exact resolveMethod?_promoted hnd1 hn' hpb (by simpa using hset)

theorem promotedCallee_mono (h : a.SubTables b) {s : Store} {fid : FuncId} {p : Promotion}
    {args : List GoValue} {x : Result (Dispatched × AccessTrace)}
    (hx : toResult (promotedCallee a s fid p args) = .ok x) :
    toResult (promotedCallee b s fid p args) = .ok x := by
  have hf := h.tablesFree_eq
  unfold promotedCallee at hx ⊢
  dsimp only at hx ⊢
  free_rw_at hf hx
  cases hu : p.unsupported with
  | some cause =>
    rw [hu] at hx; simp [toResult, throw, throwThe, MonadExceptOf.throw] at hx
  | none =>
    rw [hu] at hx; dsimp only at hx ⊢
    cases ht : p.target with
    | method f =>
      rw [ht] at hx; dsimp only at hx ⊢
      cases hfa : findFunctionIn? a.functions f with
      | none => rw [hfa] at hx; simp [toResult, throw, throwThe, MonadExceptOf.throw] at hx
      | some tf => rw [hfa] at hx; rw [h.findFunctionIn?_mono hfa]; exact hx
    | iface i =>
      rw [ht] at hx; dsimp only at hx ⊢
      cases hfa : findFunctionIn? a.functions (methodFuncId i.key p.member) with
      | none => rw [hfa] at hx; simp [toResult, stuck, throw, throwThe, MonadExceptOf.throw] at hx
      | some anchor => rw [hfa] at hx; rw [h.findFunctionIn?_mono hfa]; exact hx

theorem dynamicDispatch?_mono (h : a.SubTables b) {s : Store} {f : Func} {args : Array GoValue}
    {x : Result (Option Dispatched × AccessTrace)} (hf : f ∈ a.functions.toList)
    (hx : toResult (dynamicDispatch? a s f args) = .ok x) :
    toResult (dynamicDispatch? b s f args) = .ok x := by
  have hf' := h.tablesFree_eq
  unfold dynamicDispatch? at hx ⊢
  rw [← h.methodInfoByFuncId?_eq_of_func hf]
  free_rw_at hf' hx
  cases hm : methodInfoByFuncId? a f.id with
  | none => rw [hm] at hx; exact hx
  | some method =>
    rw [hm] at hx; dsimp only at hx ⊢
    cases hn : methodRecvInterfaceName? method with
    | none => rw [hn] at hx; exact hx
    | some _ =>
      rw [hn] at hx; dsimp only at hx ⊢
      cases h0 : args[0]? with
      | none => rw [h0] at hx; exact hx
      | some v =>
        rw [h0] at hx; (try dsimp only at hx ⊢)
        cases v with
        | interface dynTy inner =>
          (try dsimp only at hx ⊢)
          cases hr : resolveMethod? a dynTy method.id with
          | none =>
            rw [hr] at hx; dsimp only at hx
            split at hx <;> simp [toResult, throw, throwThe, MonadExceptOf.throw] at hx
          | some r =>
            rw [hr] at hx; rw [h.resolveMethod?_mono hr]; dsimp only at hx ⊢
            cases hu : r.unsupported with
            | some cause => rw [hu] at hx; exact hx
            | none =>
              rw [hu] at hx; dsimp only at hx ⊢
              cases hpe : r.path.isEmpty with
              | true =>
                simp only [hpe, ↓reduceIte] at hx ⊢
                cases ht : r.target with
                | method f' =>
                  rw [ht] at hx; dsimp only at hx ⊢
                  cases hfa : findFunctionIn? a.functions f' with
                  | none => rw [hfa] at hx; simp [toResult, stuck, throw, throwThe, MonadExceptOf.throw] at hx
                  | some tf => rw [hfa] at hx; rw [h.findFunctionIn?_mono hfa]; exact hx
                | iface i => rw [ht] at hx; exact hx
              | false =>
                simp only [hpe, Bool.false_eq_true, ↓reduceIte] at hx ⊢
                cases hra : receiverAt b s inner r.path r.adjust with
                | error e => simp only [hra, Bind.bind, Except.bind] at hx ⊢; exact hx
                | ok rt =>
                  simp only [hra, Bind.bind, Except.bind] at hx ⊢
                  cases ht : r.target with
                  | method f' =>
                    rw [ht] at hx; dsimp only at hx ⊢
                    cases hfa : findFunctionIn? a.functions f' with
                    | none => rw [hfa] at hx; simp [toResult, throw, throwThe, MonadExceptOf.throw] at hx
                    | some tf => rw [hfa] at hx; rw [h.findFunctionIn?_mono hfa]; exact hx
                  | iface i => rw [ht] at hx; exact hx
        | _ => exact hx

end ProgramCtx.SubTables

namespace TableMono

/-- `toResult` across a bind that failed: only a panic survives, and it is the result. -/
theorem toResult_bind_error {α β : Type} {e : Stop} {k : α → Except Stop β} {x : Result β}
    (hx : toResult (Except.bind (.error e) k) = .ok x) : ∃ msg, e = .panic msg ∧ x = .panic msg := by
  cases x with
  | ok v => simp only [Except.bind, toResult_eq_ok_ok] at hx; cases hx
  | panic msg => simp only [Except.bind, toResult_eq_ok_panic, Except.error.injEq] at hx; exact ⟨msg, hx, rfl⟩

theorem toResult_error_ok {α : Type} {e : Stop} {x : Result α}
    (hx : toResult (.error e : Except Stop α) = .ok x) : ∃ msg, e = .panic msg ∧ x = .panic msg := by
  cases x with
  | ok v => simp only [toResult_eq_ok_ok] at hx; cases hx
  | panic msg => simp only [toResult_eq_ok_panic, Except.error.injEq] at hx; exact ⟨msg, hx, rfl⟩

end TableMono

theorem callee?_func_inv {ctx : ProgramCtx} {fid : FuncId} {f : Func}
    (hc : callee? ctx fid = some (.func f)) : findFunctionIn? ctx.functions fid = some f := by
  unfold callee? at hc
  cases hfa : findFunctionIn? ctx.functions fid with
  | some g => rw [hfa] at hc; cases hc; rfl
  | none =>
    rw [hfa] at hc
    cases hpa : ctx.promotions.find? (fun p => methodFuncId p.type.key p.member == fid) with
    | none => rw [hpa] at hc; cases hc
    | some p => rw [hpa] at hc; cases hc

/-- The FORM of a resolution: a declared method's (empty path, no stub cause) or a record's. -/
theorem resolveMethod?_form {ctx : ProgramCtx} {t : Ty} {M : Declaration.MemberId}
    {r : MethodResolution} (hr : resolveMethod? ctx t M = some r) :
    (∃ info adj, r = .declared adj info) ∨ (∃ p ∈ ctx.promotions.toList, r = .ofPromotion p) := by
  unfold resolveMethod? at hr
  split at hr
  · cases hr; exact .inl ⟨_, _, rfl⟩
  · split at hr
    · cases hr
    · cases hr
    · split at hr
      · cases hr; exact .inl ⟨_, _, rfl⟩
      · obtain ⟨_, _, p, -, -, hp, -, rfl⟩ := ProgramCtx.SubTables.resolvePromoted?_inv hr
        exact .inr ⟨p, by simpa using (promotion?_some hp).2.2, rfl⟩
    · obtain ⟨_, _, p, -, -, hp, -, rfl⟩ := ProgramCtx.SubTables.resolvePromoted?_inv hr
      exact .inr ⟨p, by simpa using (promotion?_some hp).2.2, rfl⟩

namespace ProgramCtx.SubTables
variable {a b : ProgramCtx}

theorem enterFrame_plan_mono (h : a.SubTables b) {s : Store} {fid : FuncId} {args : List GoValue}
    {x : Result (Commit (Entry × Store × AccessTrace))}
    (hx : toResult (enterFrame.plan a s fid args) = .ok x) :
    toResult (enterFrame.plan b s fid args) = .ok x := by
  have hf := h.tablesFree_eq
  unfold enterFrame.plan at hx ⊢
  free_rw_at hf hx
  cases hc : callee? a fid with
  | none =>
    rw [hc] at hx
    simp [toResult, stuck, throw, throwThe, MonadExceptOf.throw, Bind.bind, Except.bind] at hx
  | some c =>
    rw [hc] at hx; rw [h.callee?_mono hc]
    cases c with
    | func func =>
      dsimp only at hx ⊢
      have hfunc : func ∈ a.functions.toList := by
        simpa using (findFunctionIn?_some (callee?_func_inv hc)).2
      cases hsz : (func.args.size != args.length) with
      | true =>
        simp only [hsz, ↓reduceIte] at hx
        simp [toResult, stuck, throw, throwThe, MonadExceptOf.throw, Bind.bind, Except.bind] at hx
      | false =>
        simp only [hsz, Bool.false_eq_true, ↓reduceIte] at hx ⊢
        cases hd : dynamicDispatch? a s func args.toArray with
        | error e =>
          rw [hd] at hx
          obtain ⟨msg, rfl, rfl⟩ := toResult_bind_error (α := Option Dispatched × AccessTrace) hx
          have hb := h.dynamicDispatch?_mono hfunc (x := .panic msg) (by rw [hd]; rfl)
          rw [toResult_eq_ok_panic.mp hb]
          rfl
        | ok dt =>
          rw [hd] at hx
          have hb := h.dynamicDispatch?_mono hfunc (x := .ok dt) (by rw [hd]; rfl)
          rw [toResult_eq_ok_ok.mp hb]
          exact hx
    | promotion p =>
      dsimp only at hx ⊢
      cases hp : promotedCallee a s fid p args with
      | error e =>
        rw [hp] at hx
        obtain ⟨msg, rfl, rfl⟩ := toResult_bind_error (α := Dispatched × AccessTrace) hx
        have hb := h.promotedCallee_mono (x := .panic msg) (by rw [hp]; rfl)
        rw [toResult_eq_ok_panic.mp hb]
        rfl
      | ok dt =>
        rw [hp] at hx
        have hb := h.promotedCallee_mono (x := .ok dt) (by rw [hp]; rfl)
        rw [toResult_eq_ok_ok.mp hb]
        exact hx

/-- An entry that PANICKED under the slice panicked in its dispatch (the only phase of the plan
that can raise a Go panic; the binding runs in the commit). -/
theorem plan_panic_dispatch {ctx : ProgramCtx} {s : Store} {fid : FuncId} {args : List GoValue}
    {func : Func} {m : String} (hc : callee? ctx fid = some (.func func))
    (hpan : enterFrame.plan ctx s fid args = .error (.panic m)) :
    (func.args.size != args.length) = false ∧
      dynamicDispatch? ctx s func args.toArray = .error (.panic m) := by
  unfold enterFrame.plan at hpan
  rw [hc] at hpan; dsimp only at hpan
  cases hsz : (func.args.size != args.length) with
  | true =>
    simp only [hsz, ↓reduceIte] at hpan
    simp [stuck, throw, throwThe, MonadExceptOf.throw, Bind.bind, Except.bind] at hpan
  | false =>
    simp only [hsz, Bool.false_eq_true, ↓reduceIte] at hpan
    refine ⟨rfl, ?_⟩
    cases hd : dynamicDispatch? ctx s func args.toArray with
    | error e => rw [hd] at hpan; simpa [Bind.bind, Except.bind] using hpan
    | ok dt =>
      rw [hd] at hpan
      obtain ⟨d, tr⟩ := dt
      simp only [Bind.bind, Except.bind, pure, Except.pure] at hpan
      rcases d with _ | (⟨fid', args'⟩ | ⟨func', args'⟩)
      all_goals (dsimp only at hpan)
      all_goals (try split at hpan)
      all_goals simp [stuck, throw, throwThe, MonadExceptOf.throw, Bind.bind, Except.bind] at hpan

/-- On the panic path of an entry, the `nilValueMethodText` family answer agrees: every lookup
it makes was positive under the slice, or the entry would have refused instead of panicking. -/
theorem nilValueMethodText?_eq_of_panic (h : a.SubTables b) {s : Store} {fid : FuncId}
    {args : List GoValue} {m : String} (hpan : enterFrame.plan a s fid args = .error (.panic m)) :
    nilValueMethodText? a fid args = nilValueMethodText? b fid args := by
  have hf := h.tablesFree_eq
  unfold nilValueMethodText?
  simp only [symbolKeyForMessage_eq hf]
  cases hfa : findFunctionIn? a.functions fid with
  | none =>
    have hnb : findFunctionIn? b.functions fid = none := by
      unfold enterFrame.plan callee? at hpan
      rw [hfa] at hpan
      cases hpa : a.promotions.find? (fun p => methodFuncId p.type.key p.member == fid) with
      | none =>
        rw [hpa] at hpan
        simp [stuck, throw, throwThe, MonadExceptOf.throw, Bind.bind, Except.bind] at hpan
      | some p =>
        have hpb := h.mem_promotions (by simpa using Array.mem_of_find?_eq_some hpa)
        have hp := Array.find?_some hpa
        have hid : methodFuncId p.type.key p.member = fid := FuncId.beq_sound hp
        rw [← hid]; exact h.keyed.promotionNoFunc p hpb
    rw [hnb]
  | some func =>
    rw [h.findFunctionIn?_mono hfa]
    dsimp only
    have hfunc : func ∈ a.functions.toList := by simpa using (findFunctionIn?_some hfa).2
    have hc : callee? a fid = some (.func func) := by unfold callee?; rw [hfa]
    obtain ⟨hsz, hdd⟩ := plan_panic_dispatch hc hpan
    rw [← h.methodInfoByFuncId?_eq_of_func hfunc]
    simp only [hsz, Bool.false_eq_true, ↓reduceIte]
    cases hm : methodInfoByFuncId? a func.id with
    | none => rfl
    | some method =>
      dsimp only
      cases hn : methodRecvInterfaceName? method with
      | none => rfl
      | some v =>
        dsimp only
        split
        all_goals try rfl
        rename_i elem hh
        have h0 : args.toArray[0]? = some (.interface (.pointer elem) .nil) := by
          rw [List.getElem?_toArray, ← List.head?_eq_getElem?]; exact hh
        unfold dynamicDispatch? at hdd
        rw [hm] at hdd; dsimp only at hdd
        rw [hn] at hdd; dsimp only at hdd
        rw [h0] at hdd; dsimp only at hdd
        cases hr : resolveMethod? a (.pointer elem) method.id with
        | none =>
          exfalso
          rw [hr] at hdd; dsimp only at hdd
          split at hdd <;> simp [throw, throwThe, MonadExceptOf.throw] at hdd
        | some r =>
          rw [hr] at hdd; dsimp only at hdd
          rw [h.resolveMethod?_mono hr]
          rcases resolveMethod?_form hr with ⟨info, adj, rfl⟩ | ⟨p, hp, rfl⟩
          · -- declared: the empty path; the target is the method's own id
            have hempty : (#[] : Array PromotionHop).isEmpty = true := rfl
            simp only [MethodResolution.declared, hempty, Bool.true_and] at hdd ⊢
            cases adj with
            | deref =>
              have hadj : (PromotionAdjust.deref == PromotionAdjust.deref) = true := by decide
              simp only [hadj, ↓reduceIte]
              cases hff : findFunctionIn? a.functions info.funcId with
              | none =>
                exfalso
                simp only [↓reduceIte, hff] at hdd
                simp [stuck, throw, throwThe, MonadExceptOf.throw] at hdd
              | some tf => rw [h.findFunctionIn?_mono hff]
            | asIs =>
              have hadj : (PromotionAdjust.asIs == PromotionAdjust.deref) = false := by decide
              simp only [hadj, Bool.false_eq_true, ↓reduceIte]
            | addr =>
              have hadj : (PromotionAdjust.addr == PromotionAdjust.deref) = false := by decide
              simp only [hadj, Bool.false_eq_true, ↓reduceIte]
          · -- a record: its path is not empty
            have hpath : p.path.isEmpty = false := h.keyed.promotionPath p (h.mem_promotions hp)
            simp only [MethodResolution.ofPromotion, hpath, Bool.false_and, Bool.false_eq_true,
              ↓reduceIte]

theorem enterFramePickV_mono (h : a.SubTables b) {s : Store} {fid : FuncId} {args : List GoValue}
    {ch : Choices} {x : Result (Commit (Entry × Store × AccessTrace)) × Choices × List PickRecord}
    (hx : enterFramePickV a s fid args ch = .ok x) : enterFramePickV b s fid args ch = .ok x := by
  unfold enterFramePickV at hx ⊢
  cases hp : toResult (enterFrame.plan a s fid args) with
  | error e => rw [hp] at hx; cases hx
  | ok r =>
    rw [hp] at hx; rw [h.enterFrame_plan_mono hp]
    cases r with
    | ok c => exact hx
    | panic msg =>
      have hnv := h.nilValueMethodText?_eq_of_panic (toResult_eq_ok_panic.mp hp)
      unfold nilValueMethodWidth entryPanicText at hx ⊢
      rw [hnv] at hx; exact hx

theorem preprintDispatch_mono (h : a.SubTables b) {s : Store} {e : PanicEntry}
    {x : Result (FuncId × GoValue × AccessTrace)}
    (hx : toResult (preprintDispatch a s e) = .ok x) : toResult (preprintDispatch b s e) = .ok x := by
  have hf := h.tablesFree_eq
  unfold preprintDispatch at hx ⊢
  free_rw_at hf hx
  cases hw : e.rewrite with
  | pending M =>
    rw [hw] at hx; dsimp only at hx ⊢
    cases hv : e.value with
    | interface dynTy inner =>
      rw [hv] at hx; dsimp only at hx ⊢
      cases hr : resolveMethod? a dynTy M with
      | none => rw [hr] at hx; simp [toResult, throw, throwThe, MonadExceptOf.throw] at hx
      | some r =>
        rw [hr] at hx; rw [h.resolveMethod?_mono hr]; exact hx
    | _ => rw [hv] at hx; simp [toResult, throw, throwThe, MonadExceptOf.throw] at hx
  | _ => rw [hw] at hx; simp [toResult, throw, throwThe, MonadExceptOf.throw] at hx

theorem stepNextOther_mono (h : a.SubTables b) {s : Store} {k : Cont} {ch : Choices}
    {r : Config × Store × Choices × StepLabel} (hx : stepNextOther a s k ch = .ok r) :
    stepNextOther b s k ch = .ok r := by
  unfold stepNextOther at hx ⊢
  cases k with
  | nil => exact hx
  | cons fr k' =>
    cases fr with
    | preprintK older entry newer =>
      dsimp only at hx ⊢
      cases hd : toResult (preprintDispatch a s entry) with
      | error e => rw [hd] at hx; simp [Bind.bind, Except.bind] at hx
      | ok rr => rw [hd] at hx; rw [h.preprintDispatch_mono hd]; exact hx
    | _ => exact hx

theorem stepFrameExit_mono (h : a.SubTables b) {s : Store} {targets : List (TargetShape × List Expr)}
    {tenv : LocalEnv} {results : List Loc} {ds : List (GoValue × List GoValue)} {k' : Cont} {fr : FuncId}
    {ch : Choices} {r : Config × Store × Choices × StepLabel}
    (hx : stepFrameExit a s targets tenv results ds k' fr ch = .ok r) :
    stepFrameExit b s targets tenv results ds k' fr ch = .ok r := by
  have hf := h.tablesFree_eq
  unfold stepFrameExit at hx ⊢
  free_rw_at hf hx
  rcases ds with _ | ⟨⟨cv, dargs⟩, ds⟩
  · -- the four result arms: table-free
    split
    all_goals (try contradiction)
    all_goals (try (dsimp only at hx; exact hx))
    all_goals (try exact hx)
  · -- the defer-drain arm: the one entry position
    rcases targets with _ | ⟨⟨sh, _ | ⟨e, ops⟩⟩, rest⟩ <;> rcases results with _ | ⟨rl, rls⟩ <;>
      (dsimp only at hx ⊢
       cases cv <;> (try exact hx)
       case funcVal fid captured =>
         (try dsimp only at hx ⊢)
         cases he : enterFramePickV a s fid (captured ++ dargs) ch with
         | error e => rw [he] at hx; simp [Bind.bind, Except.bind] at hx
         | ok y => rw [he] at hx; rw [h.enterFramePickV_mono he]; exact hx)

end ProgramCtx.SubTables
namespace TableMono

/-- A helper's answer a successful step lets through (`toResult`): a value or a Go panic —
never a refusal, a fatal, a deadlock or fuel exhaustion. -/
def Passes {α : Type} (x : Except Stop α) : Prop := ∃ y, toResult x = .ok y

theorem passes_ok {α : Type} {v : α} : Passes (.ok v : Except Stop α) := ⟨_, rfl⟩

theorem passes_of_toResult {α : Type} {x : Except Stop α} {y : Result α}
    (hx : toResult x = .ok y) : Passes x := ⟨y, hx⟩

/-- A passing answer is a value or a panic. -/
theorem passes_cases {α : Type} {x : Except Stop α} (hp : Passes x) :
    (∃ v, x = .ok v) ∨ ∃ msg, x = .error (.panic msg) := by
  obtain ⟨y, hy⟩ := hp
  cases y with
  | ok v => exact .inl ⟨v, toResult_eq_ok_ok.mp hy⟩
  | panic msg => exact .inr ⟨msg, toResult_eq_ok_panic.mp hy⟩

theorem passes_error {α : Type} {x : Except Stop α} {e : Stop} (hp : Passes x)
    (hx : x = .error e) : ∃ msg, e = .panic msg := by
  rcases passes_cases hp with ⟨v, rfl⟩ | ⟨msg, rfl⟩
  · cases hx
  · exact ⟨msg, (Except.error.inj hx).symm⟩

/-- A passing bind passes its first action. -/
theorem passes_bind {α β : Type} {x : Except Stop α} {k : α → Except Stop β}
    (hp : Passes (x >>= k)) : Passes x := by
  cases hx : x with
  | ok v => exact passes_ok
  | error e =>
    rw [hx] at hp
    obtain ⟨msg, rfl⟩ := passes_error hp (show (Except.error e >>= k : Except Stop β) = .error e from rfl)
    exact ⟨.panic msg, rfl⟩

/-- A passing bind whose first action is a value passes its continuation. -/
theorem passes_bind_ok {α β : Type} {x : Except Stop α} {k : α → Except Stop β} {v : α}
    (hp : Passes (x >>= k)) (hx : x = .ok v) : Passes (k v) := by
  rw [hx] at hp; simpa [Bind.bind, Except.bind] using hp

theorem passes_map {α β : Type} {x : Except Stop α} {g : α → β}
    (hp : Passes (Except.map g x)) : Passes x := by
  cases hx : x with
  | ok v => exact passes_ok
  | error e =>
    rw [hx] at hp
    obtain ⟨msg, rfl⟩ := passes_error hp (show Except.map g (.error e : Except Stop α) = .error e from rfl)
    exact ⟨.panic msg, rfl⟩

/-- A passing `Except` that never panics is a value. -/
theorem passes_ok_of_noPanic {α : Type} {x : Except Stop α} (hp : Passes x)
    (hnp : ∀ msg, x ≠ .error (.panic msg)) : ∃ v, x = .ok v := by
  rcases passes_cases hp with h | ⟨msg, h⟩
  · exact h
  · exact absurd h (hnp msg)

theorem bind_ok_eq {α β : Type} (x : α) (k : α → Except Stop β) :
    ((.ok x : Except Stop α) >>= k) = k x := rfl
theorem bind_error_eq {α β : Type} (e : Stop) (k : α → Except Stop β) :
    ((.error e : Except Stop α) >>= k) = .error e := rfl
theorem pure_ok {α : Type} (x : α) : (pure x : Except Stop α) = .ok x := rfl
theorem unsupported_eq {α : Type} (m : String) : (unsupported m : Except Stop α) = .error (.unsupported m) := rfl

/-- Two binds on the same first action agree when their continuations agree on every value the
action passes to them. -/
theorem bind_congr_passes {α β : Type} {x : Except Stop α} {k k' : α → Except Stop β}
    (hp : Passes (x >>= k)) (hk : ∀ v, x = .ok v → Passes (k v) → k v = k' v) :
    x >>= k = x >>= k' := by
  cases hx : x with
  | error e => rfl
  | ok v => simp only [bind_ok_eq]; exact hk v hx (passes_bind_ok hp hx)

/-- Through a bind on `toResult`: a passing first action that AGREES on the two contexts gives
the same successful step. -/
theorem bind_toResult_mono {α β : Type} {f g : Except Stop α} {k : Result α → Except Stop β} {r : β}
    (hfg : Passes f → f = g) (hx : toResult f >>= k = .ok r) : toResult g >>= k = .ok r := by
  cases hf : toResult f with
  | error e => rw [hf] at hx; simp [Bind.bind, Except.bind] at hx
  | ok v => rw [← hfg ⟨v, hf⟩]; exact hx

/-- `firstUnsatisfiedMethod?`'s fold, through its two equations (the matcher is the
definition's own; a client states the equations by `rfl`): an answer stays; `none` exactly when
every requirement is met; a `some` is an unmet member. -/
theorem firstMissing_foldl_some {α : Type} {f : Option α → α → Option α}
    (hsome : ∀ x r, f (some x) r = some x) (l : List α) (x : α) : l.foldl f (some x) = some x := by
  induction l with
  | nil => rfl
  | cons r rs ih => rw [List.foldl_cons, hsome]; exact ih

theorem firstMissing_foldl_none {α : Type} {f : Option α → α → Option α} {sat : α → Bool}
    (hsome : ∀ x r, f (some x) r = some x) (hnone : ∀ r, f none r = if sat r then none else some r)
    (l : List α) (h : l.foldl f none = none) : ∀ r ∈ l, sat r = true := by
  induction l with
  | nil => simp
  | cons r rs ih =>
    rw [List.foldl_cons, hnone] at h
    cases hs : sat r
    · rw [hs] at h; simp only [Bool.false_eq_true, ↓reduceIte] at h
      rw [firstMissing_foldl_some hsome] at h; cases h
    · rw [hs] at h; simp only [↓reduceIte] at h
      intro q hq
      rcases List.mem_cons.mp hq with rfl | hq
      · exact hs
      · exact ih h q hq

theorem firstMissing_foldl_none_of_all {α : Type} {f : Option α → α → Option α} {sat : α → Bool}
    (hnone : ∀ r, f none r = if sat r then none else some r)
    (l : List α) (h : ∀ r ∈ l, sat r = true) : l.foldl f none = none := by
  induction l with
  | nil => rfl
  | cons r rs ih =>
    rw [List.foldl_cons, hnone, h r (List.mem_cons_self ..)]
    simp only [↓reduceIte]
    exact ih fun q hq => h q (List.mem_cons_of_mem _ hq)

theorem firstMissing_foldl_some_mem {α : Type} {f : Option α → α → Option α} {sat : α → Bool}
    (hsome : ∀ x r, f (some x) r = some x) (hnone : ∀ r, f none r = if sat r then none else some r)
    (l : List α) {q : α} (h : l.foldl f none = some q) : q ∈ l ∧ sat q = false := by
  induction l with
  | nil => cases h
  | cons r rs ih =>
    rw [List.foldl_cons, hnone] at h
    cases hs : sat r
    · rw [hs] at h; simp only [Bool.false_eq_true, ↓reduceIte] at h
      rw [firstMissing_foldl_some hsome] at h
      cases h
      exact ⟨List.mem_cons_self .., hs⟩
    · rw [hs] at h; simp only [↓reduceIte] at h
      obtain ⟨hm, hq⟩ := ih h
      exact ⟨List.mem_cons_of_mem _ hm, hq⟩

end TableMono

open TableMono

/-- `methodCarrierKey?` of `*T` is `T`'s, for a non-pointer `T` (the base is the same). -/
theorem methodCarrierKey?_pointer (c : ProgramCtx) {elem : Ty} (hne : ∀ e, elem ≠ .pointer e) :
    methodCarrierKey? c (.pointer elem) = methodCarrierKey? c elem := by
  cases elem <;> first | rfl | exact absurd rfl (hne _)

theorem dynamicMethodSetRecorded_pointer (c : ProgramCtx) {elem : Ty} (hne : ∀ e, elem ≠ .pointer e) :
    dynamicMethodSetRecorded c (.pointer elem) = dynamicMethodSetRecorded c elem := by
  unfold dynamicMethodSetRecorded; rw [methodCarrierKey?_pointer c hne]

/-- The record of `*T` certifies `T` (a non-pointer `T`: the element of the box `resolveMethod?`
dereferences). -/
theorem dynamicMethodSetRecorded_of_pointer {c : ProgramCtx} {elem : Ty}
    (hr : dynamicMethodSetRecorded c (.pointer elem) = true)
    (hne : match elem with | .pointer _ => False | _ => True) :
    dynamicMethodSetRecorded c elem = true := by
  cases elem <;> first | exact hne.elim | (rwa [dynamicMethodSetRecorded_pointer c (fun _ h => by cases h)] at hr)

/-- `methodCarrierKey?` of a defined type is its name's key. -/
theorem methodCarrierKey?_defined {c : ProgramCtx} {idx : TypeIdx} {carrier : TypeId}
    (hn : c.types.nameOf? idx = some carrier) : methodCarrierKey? c (.defined idx) = some carrier.key := by
  simp [methodCarrierKey?, hn]

theorem methodCarrierKey?_pointer_defined {c : ProgramCtx} {idx : TypeIdx} {carrier : TypeId}
    (hn : c.types.nameOf? idx = some carrier) :
    methodCarrierKey? c (.pointer (.defined idx)) = some carrier.key := by
  simp [methodCarrierKey?, hn]

namespace ProgramCtx.SubTables
variable {a b : ProgramCtx}

/-! ### The record: present in the slice ⇒ present in the whole, and it certifies the carrier -/

theorem dynamicMethodSetRecorded_mono (h : a.SubTables b) {t : Ty}
    (hr : dynamicMethodSetRecorded a t = true) : dynamicMethodSetRecorded b t = true := by
  unfold dynamicMethodSetRecorded at hr ⊢
  rw [methodCarrierKey?_eq h.tablesFree_eq] at hr
  cases hk : methodCarrierKey? b t with
  | none => rfl
  | some key =>
    rw [hk] at hr
    obtain ⟨cov, hc⟩ := Option.isSome_iff_exists.mp hr
    simp [h.methodSetCoverage?_mono hc]

/-- The slice's record of a carrier key it answers for. -/
theorem record_of_recorded (h : a.SubTables b) {t : Ty} {key : String}
    (hk : methodCarrierKey? b t = some key) (hr : dynamicMethodSetRecorded a t = true) :
    ∃ r ∈ a.methodSets.toList, r.key = key := by
  unfold dynamicMethodSetRecorded at hr
  rw [methodCarrierKey?_eq h.tablesFree_eq, hk] at hr
  obtain ⟨cov, hc⟩ := Option.isSome_iff_exists.mp hr
  exact record_of_coverage hc

theorem dynamicMethodSetExportedOnly_eq_of_recorded (h : a.SubTables b) {t : Ty}
    (hr : dynamicMethodSetRecorded a t = true) :
    dynamicMethodSetExportedOnly a t = dynamicMethodSetExportedOnly b t := by
  unfold dynamicMethodSetRecorded at hr
  unfold dynamicMethodSetExportedOnly
  rw [methodCarrierKey?_eq h.tablesFree_eq] at hr ⊢
  cases hk : methodCarrierKey? b t with
  | none => rfl
  | some key =>
    rw [hk] at hr
    obtain ⟨cov, hc⟩ := Option.isSome_iff_exists.mp hr
    simp only [hc, h.methodSetCoverage?_mono hc]

/-! ### Declarations and promotions on a recorded carrier: the same under both -/

theorem methodDecl?_eq_of_recorded (h : a.SubTables b) {t : Ty} {M : Declaration.MemberId}
    (hr : dynamicMethodSetRecorded a t = true) : methodDecl? a t M = methodDecl? b t M := by
  cases hb : methodDecl? b t M with
  | none =>
    cases ha : methodDecl? a t M with
    | none => rfl
    | some m => have := h.methodDecl?_mono ha; rw [hb] at this; cases this
  | some m =>
    obtain ⟨-, hrecv, hmb⟩ := methodDecl?_some' hb
    obtain ⟨key, hk⟩ := Option.isSome_iff_exists.mp (h.keyed.recvCarrier m hmb t hrecv)
    obtain ⟨r, hra, hrk⟩ := h.record_of_recorded hk hr
    have hma : m ∈ a.methods.toList :=
      (h.closed.recordMethods r hra m hmb t hrecv (by rw [hrk]; exact hk)).1
    obtain ⟨h1, h2, -⟩ := methodDecl?_some hb
    obtain ⟨m', hm'⟩ : ∃ m', methodDecl? a t M = some m' := by
      rw [methodDecl?_eq_find?]
      cases hfa : a.methods.toList.find?
          (fun method => method.id == M && methodRecvDynamicTy? method == some t) with
      | some m' => exact ⟨m', rfl⟩
      | none =>
        exact absurd (by simp only [Bool.and_eq_true]; exact ⟨h1, h2⟩)
          (List.find?_eq_none.mp hfa m hma)
    have := h.methodDecl?_mono hm'
    rw [hb] at this
    rw [hm']; exact this.symm

theorem promotion?_eq_of_recorded (h : a.SubTables b) {idx : TypeIdx} {carrier : TypeId}
    {M : Declaration.MemberId} (hn : b.types.nameOf? idx = some carrier)
    (hr : dynamicMethodSetRecorded a (.defined idx) = true) :
    promotion? a carrier M = promotion? b carrier M := by
  cases hb : promotion? b carrier M with
  | none =>
    cases ha : promotion? a carrier M with
    | none => rfl
    | some p => have := h.promotion?_mono ha; rw [hb] at this; cases this
  | some p =>
    obtain ⟨hc, hM, hpb'⟩ := promotion?_some hb
    have hpb : p ∈ b.promotions.toList := by simpa using hpb'
    obtain ⟨r, hra, hrk⟩ := h.record_of_recorded (methodCarrierKey?_defined hn) hr
    have hpa : p ∈ a.promotions.toList :=
      (h.closed.recordPromotions r hra p hpb (by rw [hc, hrk])).1
    obtain ⟨p', hp'⟩ : ∃ p', promotion? a carrier M = some p' := by
      rw [promotion?_eq_find?]
      cases hfa : a.promotions.toList.find? (fun q => q.type == carrier && q.member == M) with
      | some p' => exact ⟨p', rfl⟩
      | none =>
        exact absurd (by simp only [Bool.and_eq_true, beq_iff_eq]; exact ⟨hc, hM⟩)
          (List.find?_eq_none.mp hfa p hpa)
    have := h.promotion?_mono hp'
    rw [hb] at this
    rw [hp']; exact this.symm

theorem resolvePromoted?_eq_of_recorded (h : a.SubTables b) {base : Ty} {ptr : Bool}
    {M : Declaration.MemberId} (hr : dynamicMethodSetRecorded a base = true) :
    resolvePromoted? a base ptr M = resolvePromoted? b base ptr M := by
  unfold resolvePromoted?
  rw [types_eq h.tablesFree_eq]
  cases base with
  | defined idx =>
    dsimp only
    cases hn : b.types.nameOf? idx with
    | none => rfl
    | some carrier => simp only [h.promotion?_eq_of_recorded hn hr]
  | _ => rfl

theorem resolveMethod?_eq_of_recorded (h : a.SubTables b) {t : Ty} {M : Declaration.MemberId}
    (hr : dynamicMethodSetRecorded a t = true) : resolveMethod? a t M = resolveMethod? b t M := by
  unfold resolveMethod?
  rw [h.methodDecl?_eq_of_recorded hr]
  cases methodDecl? b t M with
  | some _ => rfl
  | none =>
    cases t with
    | pointer elem =>
      cases elem with
      | pointer _ => rfl
      | interface _ => rfl
      | _ =>
        have hr' := dynamicMethodSetRecorded_of_pointer hr trivial
        simp only [h.methodDecl?_eq_of_recorded hr', h.resolvePromoted?_eq_of_recorded hr']
    | _ => simp only [h.resolvePromoted?_eq_of_recorded hr]

/-! ### Signatures: the kept `Func`s of a recorded carrier -/

theorem findFunctionIn?_eq_of_kept (h : a.SubTables b) {f : FuncId}
    (hk : ∀ g ∈ b.functions.toList, g.id = f → g ∈ a.functions.toList) :
    findFunctionIn? a.functions f = findFunctionIn? b.functions f := by
  cases hb : findFunctionIn? b.functions f with
  | none =>
    cases ha : findFunctionIn? a.functions f with
    | none => rfl
    | some g => have := h.findFunctionIn?_mono ha; rw [hb] at this; cases this
  | some g =>
    have hg := findFunctionIn?_some hb
    have hga : g ∈ a.functions.toList := hk g (by simpa using hg.2) (FuncId.beq_sound hg.1)
    obtain ⟨g', hg'⟩ : ∃ g', findFunctionIn? a.functions f = some g' := by
      rw [findFunctionIn?_eq_find?]
      cases hfa : a.functions.toList.find? (fun func => func.id == f) with
      | some g' => exact ⟨g', rfl⟩
      | none => exact absurd hg.1 (List.find?_eq_none.mp hfa g hga)
    have := h.findFunctionIn?_mono hg'
    rw [hb] at this
    rw [hg']; exact this.symm

theorem funcSignature?_eq_of_kept (h : a.SubTables b) {f : FuncId}
    (hk : ∀ g ∈ b.functions.toList, g.id = f → g ∈ a.functions.toList) :
    funcSignature? a f = funcSignature? b f := by
  delta funcSignature?; rw [h.findFunctionIn?_eq_of_kept hk]

/-- A found signature is found the same under the whole (positive lookups only). -/
theorem funcSignature?_mono (h : a.SubTables b) {f : FuncId} {sg : Array Ty × Array Ty × Bool}
    (hs : funcSignature? a f = some sg) : funcSignature? b f = some sg := by
  unfold funcSignature? at hs ⊢
  cases hf : findFunctionIn? a.functions f with
  | none => rw [hf] at hs; cases hs
  | some fn => rw [hf] at hs; rw [h.findFunctionIn?_mono hf]; exact hs

theorem resolvedSignature?_mono (h : a.SubTables b) {M : Declaration.MemberId} {r : MethodResolution}
    {sg : Array Ty × Array Ty × Bool} (hs : resolvedSignature? a M r = some sg) :
    resolvedSignature? b M r = some sg := by
  unfold resolvedSignature? at hs ⊢
  rw [interfaceDeclaredMethods?_eq h.tablesFree_eq] at hs
  cases hsig : r.sig with
  | some _ => simp only [hsig] at hs ⊢; exact hs
  | none =>
    simp only [hsig] at hs ⊢
    cases ht : r.target with
    | method f => simp only [ht] at hs ⊢; exact h.funcSignature?_mono hs
    | iface i => simp only [ht] at hs ⊢; exact hs

end ProgramCtx.SubTables

/-- Where a resolution's callable target comes from, with the CARRIER it was found on: a declared
method of the dynamic type or of the pointer's element (both share the carrier key), or the
carrier's promotion record. -/
theorem resolveMethod?_target' {ctx : ProgramCtx} {t : Ty} {M : Declaration.MemberId}
    {r : MethodResolution} (hr : resolveMethod? ctx t M = some r) :
    (∃ m ∈ ctx.methods.toList, (∃ u, methodRecvDynamicTy? m = some u ∧
        methodCarrierKey? ctx u = methodCarrierKey? ctx t) ∧
      r.target = .method m.funcId ∧ r.sig = none) ∨
    (∃ idx carrier p, methodCarrierKey? ctx t = some carrier.key ∧ ctx.types.nameOf? idx = some carrier ∧
      p ∈ ctx.promotions.toList ∧ p.type = carrier ∧ r.target = p.target ∧ r.sig = p.sig) := by
  have hprom : ∀ {base : Ty} {ptr : Bool}, resolvePromoted? ctx base ptr M = some r →
      ∃ idx carrier p, base = .defined idx ∧ ctx.types.nameOf? idx = some carrier ∧
        p ∈ ctx.promotions.toList ∧ p.type = carrier ∧ r.target = p.target ∧ r.sig = p.sig := by
    intro base ptr hp
    unfold resolvePromoted? at hp
    split at hp
    · split at hp
      · split at hp
        · split at hp
          · cases hp
          · obtain ⟨h1, -, h3⟩ := promotion?_some ‹_›
            cases hp
            exact ⟨_, _, _, rfl, ‹_›, by simpa using h3, h1, rfl, rfl⟩
        · cases hp
      · cases hp
    · cases hp
  unfold resolveMethod? at hr
  split at hr
  · obtain ⟨-, hrecv, hmem⟩ := ProgramCtx.SubTables.methodDecl?_some' ‹_›
    cases hr
    exact .inl ⟨_, hmem, ⟨t, hrecv, rfl⟩, rfl, rfl⟩
  · split at hr
    · cases hr
    · cases hr
    · rename_i elem hne1 hne2 hd
      split at hr
      · obtain ⟨-, hrecv, hmem⟩ := ProgramCtx.SubTables.methodDecl?_some' ‹_›
        cases hr
        refine .inl ⟨_, hmem, ⟨elem, hrecv, ?_⟩, rfl, rfl⟩
        rw [methodCarrierKey?_pointer ctx]
        intro e he; subst he; exact hne1 e rfl
      · obtain ⟨idx, carrier, p, rfl, hn, hp, hpc, ht, hs⟩ := hprom hr
        exact .inr ⟨idx, carrier, p, methodCarrierKey?_pointer_defined hn, hn, hp, hpc, ht, hs⟩
    · obtain ⟨idx, carrier, p, rfl, hn, hp, hpc, ht, hs⟩ := hprom hr
      exact .inr ⟨idx, carrier, p, methodCarrierKey?_defined hn, hn, hp, hpc, ht, hs⟩

namespace ProgramCtx.SubTables
variable {a b : ProgramCtx}

theorem resolvedSignature?_eq_of_recorded (h : a.SubTables b) {t : Ty} {M : Declaration.MemberId}
    {r : MethodResolution} (hr : dynamicMethodSetRecorded a t = true)
    (hres : resolveMethod? b t M = some r) :
    resolvedSignature? a M r = resolvedSignature? b M r := by
  delta resolvedSignature?
  simp only [interfaceDeclaredMethods?_eq h.tablesFree_eq]
  rcases resolveMethod?_target' hres with ⟨m, hm, ⟨u, hu, hku⟩, ht, hs⟩ | ⟨idx, carrier, p, hkt, hn, hp, hpc, ht, hs⟩
  · rw [hs, ht]
    obtain ⟨key, hk⟩ := Option.isSome_iff_exists.mp (h.keyed.recvCarrier m hm u hu)
    obtain ⟨r', hra, hrk⟩ := h.record_of_recorded (hku ▸ hk) hr
    exact h.funcSignature?_eq_of_kept (h.closed.recordMethods r' hra m hm u hu (by rw [hrk]; exact hk)).2
  · rw [hs, ht]
    cases p.sig with
    | some sg => rfl
    | none =>
      cases hpt : p.target with
      | method f =>
        obtain ⟨r', hra, hrk⟩ := h.record_of_recorded hkt hr
        exact h.funcSignature?_eq_of_kept
          ((h.closed.recordPromotions r' hra p hp (by rw [hrk, hpc])).2 f hpt)
      | iface i => rfl

theorem satisfiesMethodSig_eq_of_recorded (h : a.SubTables b) {t : Ty} {req : MethodSig}
    (hr : dynamicMethodSetRecorded a t = true) :
    satisfiesMethodSig a t req = satisfiesMethodSig b t req := by
  delta satisfiesMethodSig
  rw [h.resolveMethod?_eq_of_recorded hr]
  cases hres : resolveMethod? b t req.id with
  | none => rfl
  | some r => simp only [h.resolvedSignature?_eq_of_recorded hr hres]

/-- Satisfaction found under the slice is found under the whole (positive lookups only). -/
theorem satisfiesMethodSig_mono (h : a.SubTables b) {t : Ty} {req : MethodSig}
    (hs : satisfiesMethodSig a t req = true) : satisfiesMethodSig b t req = true := by
  unfold satisfiesMethodSig at hs ⊢
  cases hres : resolveMethod? a t req.id with
  | none => simp only [hres] at hs; cases hs
  | some r =>
    simp only [hres] at hs
    simp only [h.resolveMethod?_mono hres]
    cases hsg : resolvedSignature? a req.id r with
    | none => simp only [hsg] at hs; cases hs
    | some sg => simp only [hsg] at hs; simp only [h.resolvedSignature?_mono hsg]; exact hs

/-- A preprint member found under the slice is found under the whole (positive lookups only):
`Error()` decides the mark without the record. -/
theorem hasNoArgStringMethod_mono (h : a.SubTables b) {t : Ty} {M : Declaration.MemberId}
    (hs : hasNoArgStringMethod a t M = true) : hasNoArgStringMethod b t M = true := by
  unfold hasNoArgStringMethod at hs ⊢
  cases hres : resolveMethod? a t M with
  | none => simp only [hres] at hs; cases hs
  | some r =>
    simp only [hres] at hs
    simp only [h.resolveMethod?_mono hres]
    cases hsg : resolvedSignature? a M r with
    | none => simp only [hsg] at hs; cases hs
    | some sg => simp only [hsg] at hs; simp only [h.resolvedSignature?_mono hsg]; exact hs

theorem hasNoArgStringMethod_eq_of_recorded (h : a.SubTables b) {t : Ty} {M : Declaration.MemberId}
    (hr : dynamicMethodSetRecorded a t = true) :
    hasNoArgStringMethod a t M = hasNoArgStringMethod b t M := by
  delta hasNoArgStringMethod
  rw [h.resolveMethod?_eq_of_recorded hr]
  cases hres : resolveMethod? b t M with
  | none => rfl
  | some r => simp only [h.resolvedSignature?_eq_of_recorded hr hres]

theorem panicPayloadIsRewritten_eq_of_recorded (h : a.SubTables b) {t : Ty}
    (hr : dynamicMethodSetRecorded a t = true) :
    panicPayloadIsRewritten a t = panicPayloadIsRewritten b t := by
  delta panicPayloadIsRewritten
  rw [h.hasNoArgStringMethod_eq_of_recorded hr, h.hasNoArgStringMethod_eq_of_recorded hr]

/-! ### Satisfaction of an interface: a passing answer is the whole's -/

/-- `firstUnsatisfiedMethod?` never panics. -/
theorem firstUnsatisfiedMethod?_noPanic {c : ProgramCtx} {t : Ty} {I : TypeId} {msg : String} :
    firstUnsatisfiedMethod? c t I ≠ .error (.panic msg) := by
  unfold firstUnsatisfiedMethod?
  intro hx
  split at hx
  · cases hx
  · split at hx
    · simp [unsupported, throw, throwThe, MonadExceptOf.throw] at hx
    · dsimp only at hx
      split at hx
      · cases hx
      · split at hx
        · simp [unsupported, throw, throwThe, MonadExceptOf.throw] at hx
        · split at hx
          · simp [unsupported, throw, throwThe, MonadExceptOf.throw] at hx
          · cases hx

theorem firstUnsatisfiedMethod?_eq (h : a.SubTables b) {t : Ty} {I : TypeId}
    (hp : Passes (firstUnsatisfiedMethod? a t I)) :
    firstUnsatisfiedMethod? a t I = firstUnsatisfiedMethod? b t I := by
  obtain ⟨o, ho⟩ := passes_ok_of_noPanic hp fun _ => firstUnsatisfiedMethod?_noPanic
  have hf := h.tablesFree_eq
  unfold firstUnsatisfiedMethod? at ho ⊢
  simp only [interfaceDeclaredMethods?_eq hf, goTypeNameForMessage_eq hf] at ho ⊢
  (try dsimp only at ho ⊢)
  split at ho
  · rename_i he; simp only [he, ↓reduceIte]
  · rename_i he
    simp only [he, ↓reduceIte]
    split at ho
    · rename_i hd; first | rfl | simp only [hd]
    · rename_i reqs hd
      (try simp only [hd])
      (try dsimp only at ho ⊢)
      -- the two folds: the slice's answer, then the whole's
      split at ho
      · -- every requirement met under the slice: met under the whole
        rename_i hfa
        (try simp only [hfa])
        rw [← Array.foldl_toList] at hfa ⊢
        rw [firstMissing_foldl_none_of_all (by intro r; rfl) _ (fun r hr => h.satisfiesMethodSig_mono
          (firstMissing_foldl_none (by intro x r; rfl) (by intro r; rfl) _ hfa r hr))]
      · -- a definite «missing» answer: the slice's record certifies it, so the folds agree
        rename_i req hfa
        have hr : dynamicMethodSetRecorded a t = true := by
          cases hr : dynamicMethodSetRecorded a t
          · rw [hr] at ho; simp [unsupported, throw, throwThe, MonadExceptOf.throw] at ho
          · rfl
        simp only [h.satisfiesMethodSig_eq_of_recorded hr] at hfa
        simp only [hfa, hr, h.dynamicMethodSetRecorded_mono hr,
          h.dynamicMethodSetExportedOnly_eq_of_recorded hr, h.satisfiesMethodSig_eq_of_recorded hr]

theorem dynamicImplementsInterface_eq (h : a.SubTables b) {t : Ty} {I : TypeId}
    (hp : Passes (dynamicImplementsInterface a t I)) :
    dynamicImplementsInterface a t I = dynamicImplementsInterface b t I := by
  unfold dynamicImplementsInterface at hp ⊢
  rw [h.firstUnsatisfiedMethod?_eq (passes_bind hp)]

theorem typeAssertValue_eq (h : a.SubTables b) {v : GoValue} {ty : Ty}
    (hp : Passes (typeAssertValue a v ty)) : typeAssertValue a v ty = typeAssertValue b v ty := by
  have hf := h.tablesFree_eq
  unfold typeAssertValue at hp ⊢
  rw [defaultValue_eq hf] at hp ⊢
  cases hd : defaultValue b ty with
  | error e => simp [Bind.bind, Except.bind]
  | ok failed =>
    rw [hd] at hp
    simp only [Bind.bind, Except.bind] at hp ⊢
    cases v with
    | interface dynTy inner =>
      cases ty with
      | interface I =>
        simp only at hp ⊢
        rw [h.dynamicImplementsInterface_eq (passes_bind hp)]
      | _ => rfl
    | _ => rfl

theorem applyRhsOp_eq (h : a.SubTables b) {s : Store} {rop : RhsOp} {vs : List GoValue}
    (hp : Passes (applyRhsOp a s rop vs)) : applyRhsOp a s rop vs = applyRhsOp b s rop vs := by
  have hf := h.tablesFree_eq
  unfold applyRhsOp at hp ⊢
  free_rw hf
  free_rw_at hf hp
  split
  all_goals (try rfl)
  rw [h.typeAssertValue_eq (passes_bind hp)]

/-! ### The type-assertion panic text: `pkgpath()` under the slice's record -/

/-- A receiver base with a method under the slice has one under the whole. -/
theorem pointerMethodSetNonEmpty_mono (h : a.SubTables b) {t : Ty}
    (ha : pointerMethodSetNonEmpty a t = true) : pointerMethodSetNonEmpty b t = true := by
  unfold pointerMethodSetNonEmpty at ha ⊢
  rw [← Array.any_toList, List.any_eq_true] at ha ⊢
  obtain ⟨m, hm, hp⟩ := ha
  exact ⟨m, h.mem_methods hm, hp⟩

/-- Under the slice's record of a defined carrier, the pointer method set's emptiness agrees. -/
theorem pointerMethodSetNonEmpty_eq_of_recorded (h : a.SubTables b) {idx : TypeIdx} {carrier : TypeId}
    (hn : b.types.nameOf? idx = some carrier) (hr : dynamicMethodSetRecorded a (.defined idx) = true) :
    pointerMethodSetNonEmpty a (.defined idx) = pointerMethodSetNonEmpty b (.defined idx) := by
  cases hb : pointerMethodSetNonEmpty b (.defined idx) with
  | false =>
    cases ha : pointerMethodSetNonEmpty a (.defined idx)
    · rfl
    · have := h.pointerMethodSetNonEmpty_mono ha; rw [hb] at this; cases this
  | true =>
    unfold pointerMethodSetNonEmpty at hb ⊢
    rw [← Array.any_toList, List.any_eq_true] at hb ⊢
    obtain ⟨m, hm, hp⟩ := hb
    obtain ⟨r, hra, hrk⟩ := h.record_of_recorded (methodCarrierKey?_defined hn) hr
    cases hrecv : methodRecvDynamicTy? m with
    | none => rw [hrecv] at hp; cases hp
    | some u =>
      rw [hrecv] at hp
      have hku : methodCarrierKey? b u = some r.key := by
        rw [hrk]
        simp only [Bool.or_eq_true] at hp
        rcases hp with hu | hu <;> rw [Ty.beq_sound hu]
        · exact methodCarrierKey?_defined hn
        · exact methodCarrierKey?_pointer_defined hn
      refine ⟨m, (h.closed.recordMethods r hra m hm u hrecv hku).1, ?_⟩
      rw [hrecv]; exact hp

theorem typePkgForMessage_eq (h : a.SubTables b) {t : Ty} (hp : Passes (typePkgForMessage a t)) :
    typePkgForMessage a t = typePkgForMessage b t := by
  have hf := h.tablesFree_eq
  unfold typePkgForMessage at hp ⊢
  free_rw hf
  free_rw_at hf hp
  split
  all_goals (try rfl)
  -- the pointer arm: its element
  split
  all_goals (try rfl)
  rename_i idx
  (try dsimp only at hp)
  cases hn : b.types.nameOf? idx with
  | none => simp only [hn, unsupported_eq, bind_error_eq]
  | some id =>
    simp only [hn, pure_ok, bind_ok_eq] at hp ⊢
    cases ha : pointerMethodSetNonEmpty a (.defined idx) with
    | true => simp only [ha, h.pointerMethodSetNonEmpty_mono ha, ↓reduceIte]
    | false =>
      simp only [ha, Bool.false_eq_true, ↓reduceIte] at hp ⊢
      cases hc : methodSetCoverage? a id.key with
      | none =>
        simp only [hc] at hp
        obtain ⟨msg, hbad⟩ := passes_error hp rfl
        simp at hbad
      | some cov =>
        have hr : dynamicMethodSetRecorded a (.defined idx) = true := by
          simp [dynamicMethodSetRecorded, methodCarrierKey?, types_eq hf, hn, hc]
        rw [← h.pointerMethodSetNonEmpty_eq_of_recorded hn hr]
        simp only [ha, Bool.false_eq_true, ↓reduceIte, hc, h.methodSetCoverage?_mono hc]

/-- The text after the runtime-error guard: the target arms, then — concrete target, boxed operand,
equal displays — the two `pkgpath()` reads, each rewritten under its own `Passes`. -/
macro "assert_text_tail" h:term:max hp:ident ty:ident v:ident : tactic => `(tactic| (
  -- the target and the operand by constructor, so every match reduces on both sides; the
  -- arms without a reader close by identity
  cases $ty:ident <;> (try cases $v:ident) <;> (try dsimp only at $hp:ident ⊢) <;> (try rfl)
  -- the equal-display test, then the two `pkgpath()` reads, each rewritten under its own `Passes`
  all_goals (
    split
    all_goals (try rfl)
    rename_i hname
    (try simp only [hname, beq_self_eq_true, Bool.false_eq_true, ↓reduceIte] at $hp:ident)
    (try simp only [show (_ == _) = false from beq_eq_false_iff_ne.mpr hname, Bool.false_eq_true, ↓reduceIte] at $hp:ident)
    (try simp only [show (_ == _) = true from beq_iff_eq.mpr hname, ↓reduceIte] at $hp:ident)
    -- (`rw`'s closing `rfl` may finish a goal whose second read is context-free, e.g. `bool`)
    have heq1 := ProgramCtx.SubTables.typePkgForMessage_eq $h (TableMono.passes_bind $hp)
    rw [heq1] at $hp:ident ⊢
    all_goals (
      refine TableMono.bind_congr_passes $hp (fun pd _ hp2 => ?_)
      (try dsimp only at hp2 ⊢)
      have heq2 := ProgramCtx.SubTables.typePkgForMessage_eq $h (TableMono.passes_bind hp2)
      rw [heq2] at hp2 ⊢
      all_goals exact TableMono.bind_congr_passes hp2 (fun pt _ _ => rfl)))))

theorem typeAssertPanicMessage_eq (h : a.SubTables b) {v : GoValue} {ty : Ty} {src : Option Ty}
    {missing : Option String} (hp : Passes (typeAssertPanicMessage a v ty src missing)) :
    typeAssertPanicMessage a v ty src missing = typeAssertPanicMessage b v ty src missing := by
  have hf := h.tablesFree_eq
  unfold typeAssertPanicMessage at hp ⊢
  free_rw hf
  free_rw_at hf hp
  -- the runtime-error guard: a boxed `.defined` payload at the twin's index refuses, else the text
  split
  · -- a boxed `.defined` payload: the twin's index refuses, any other passes to the text
    (try dsimp only at hp)
    split
    all_goals rename_i hrt
    all_goals (first
      | simp only [hrt, beq_self_eq_true, Bool.false_eq_true, ↓reduceIte] at hp
      | simp only [show (_ == _) = false from beq_eq_false_iff_ne.mpr hrt, Bool.false_eq_true, ↓reduceIte] at hp)
    all_goals (first
      | done
      | (exfalso; obtain ⟨msg, hbad⟩ := passes_error (passes_bind hp) rfl; simp at hbad; done)
      | assert_text_tail h hp ty v)
  · assert_text_tail h hp ty v

theorem applyStrictOp_eq (h : a.SubTables b) {s : Store} {leafOf : Loc → Loc} {op : StrictOp}
    {vs : List GoValue} (hp : Passes (applyStrictOp a s leafOf op vs)) :
    applyStrictOp a s leafOf op vs = applyStrictOp b s leafOf op vs := by
  have hf := h.tablesFree_eq
  unfold applyStrictOp at hp ⊢
  free_rw hf
  free_rw_at hf hp
  split
  all_goals (try rfl)
  -- the type-assertion arm: `typeAssertValue`, then (on failure) satisfaction and the text
  rename_i ty src v
  rw [h.typeAssertValue_eq (passes_bind hp)]
  cases hv : typeAssertValue b v ty with
  | error e => simp only [bind_error_eq]
  | ok result =>
    have hp2 := passes_bind_ok hp (by rw [h.typeAssertValue_eq (passes_bind hp)]; exact hv)
    simp only [bind_ok_eq] at hp2 ⊢
    cases hr2 : result.2 with
    | true => simp only [hr2, ↓reduceIte]
    | false =>
      simp only [hr2, Bool.false_eq_true, ↓reduceIte] at hp2 ⊢
      split
      · rename_i I dynTy inner
        (try dsimp only at hp2)
        rw [h.firstUnsatisfiedMethod?_eq (passes_bind hp2)]
        cases hm : firstUnsatisfiedMethod? b dynTy I with
        | error e => simp only [bind_error_eq]
        | ok missing =>
          have hp3 := passes_bind_ok hp2 (by rw [h.firstUnsatisfiedMethod?_eq (passes_bind hp2)]; exact hm)
          simp only [bind_ok_eq] at hp3 ⊢
          rw [h.typeAssertPanicMessage_eq (passes_bind hp3)]
      · (try dsimp only at hp2)
        simp only [pure_ok, bind_ok_eq] at hp2 ⊢
        rw [h.typeAssertPanicMessage_eq (passes_bind hp2)]

theorem applyStrictOpPick_eq (h : a.SubTables b) {s : Store} {leafOf : Loc → Loc} {op : StrictOp}
    {vs : List GoValue} {ch : Choices} (hp : Passes (applyStrictOpPick a s leafOf op vs ch)) :
    applyStrictOpPick a s leafOf op vs ch = applyStrictOpPick b s leafOf op vs ch := by
  have hf := h.tablesFree_eq
  unfold applyStrictOpPick at hp ⊢
  cases hk : op.convKind? with
  | some kl => simp only [hk]; rw [convCapApply_eq hf]
  | none => simp only [hk] at hp ⊢; rw [h.applyStrictOp_eq (passes_map hp)]

/-! ### The abort phase: the decision, the renderers, the abort message -/

theorem phaseMark_mono (h : a.SubTables b) {v : GoValue} {r : Rewrite}
    (hx : phaseMark a v = .ok r) : phaseMark b v = .ok r := by
  have hf := h.tablesFree_eq
  unfold phaseMark at hx ⊢
  cases v with
  | interface dynTy inner =>
    simp only at hx ⊢
    split at hx
    · rename_i hrt; first | exact hx | (simp only [hrt, ↓reduceIte]; exact hx)
    · rename_i hrt
      (try simp only [hrt, Bool.false_eq_true, ↓reduceIte] at hx)
      (try simp only [hrt, Bool.false_eq_true, ↓reduceIte])
      -- `Error()` first: found under the slice, found under the whole, no record consulted
      cases he : hasNoArgStringMethod a dynTy errorMember with
      | true =>
        rw [he] at hx
        rw [h.hasNoArgStringMethod_mono he]
        exact hx
      | false =>
        rw [he] at hx
        simp only [Bool.false_eq_true, ↓reduceIte] at hx
        -- not found: the slice's record certifies the whole finds none either
        cases hr : dynamicMethodSetRecorded a dynTy with
        | false => rw [hr] at hx; simp at hx
        | true =>
          rw [hr] at hx
          rw [← h.hasNoArgStringMethod_eq_of_recorded (M := errorMember) hr,
            ← h.hasNoArgStringMethod_eq_of_recorded (M := stringerMember) hr, he,
            h.dynamicMethodSetRecorded_mono hr]
          simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hx ⊢
          exact hx
  | _ => simp at hx

theorem renderPanicRewrite_mono (h : a.SubTables b) {e : PanicEntry} {x : String × Bool}
    (hx : renderPanicRewrite a e = some x) : renderPanicRewrite b e = some x := by
  have hf := h.tablesFree_eq
  unfold renderPanicRewrite at hx ⊢
  split at hx
  · exact hx
  · cases hx
  · cases hx
  · split at hx
    · rename_i idx v kind heq
      (try simp only at hx ⊢)
      split at hx
      · cases hx
      · rename_i hrt
        (try simp only [hrt, Bool.false_eq_true, ↓reduceIte])
        cases hr : dynamicMethodSetRecorded a (.defined idx) with
        | false => rw [hr] at hx; simp at hx
        | true =>
          rw [hr] at hx
          rw [h.dynamicMethodSetRecorded_mono hr]
          simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hx ⊢
          rw [← h.panicPayloadIsRewritten_eq_of_recorded hr]
          rw [← types_eq hf, ← displayNameOfId_eq hf]
          exact hx
    · cases hx

theorem renderPanicPayload_mono (h : a.SubTables b) {e : PanicEntry} {x : String × Bool}
    (hx : renderPanicPayload a e = some x) : renderPanicPayload b e = some x := by
  unfold renderPanicPayload at hx ⊢
  split at hx
  · cases hx
  · split at hx
    · rename_i hrt; first | exact hx | (simp only [hrt, ↓reduceIte]; exact hx)
    · rename_i hrt
      first
        | exact h.renderPanicRewrite_mono hx
        | (simp only [hrt, Bool.false_eq_true, ↓reduceIte]; exact h.renderPanicRewrite_mono hx)
  · exact hx
  · exact hx
  · exact hx
  · exact h.renderPanicRewrite_mono hx

theorem renderPanicHead_mono (h : a.SubTables b) {first : PanicEntry} {rest : List PanicEntry}
    {pick : Nat} {t : String} (hx : renderPanicHead a first rest pick = some t) :
    renderPanicHead b first rest pick = some t := by
  unfold renderPanicHead at hx ⊢
  cases hr : renderPanicPayload a first with
  | none => rw [hr] at hx; cases hx
  | some x => rw [hr] at hx; rw [h.renderPanicPayload_mono hr]; exact hx

theorem abortMsg_mono (h : a.SubTables b) {first : PanicEntry} {rest : List PanicEntry} {pick : Nat}
    {t : String} (hx : abortMsg a first rest pick = .ok t) : abortMsg b first rest pick = .ok t := by
  unfold abortMsg at hx ⊢
  cases hr : renderPanicHead a first rest pick with
  | none => rw [hr] at hx; simp [throw, throwThe, MonadExceptOf.throw] at hx
  | some msg => rw [hr] at hx; rw [h.renderPanicHead_mono hr]; exact hx

theorem stepPanicStop_mono (h : a.SubTables b) {s : Store} {first : PanicEntry} {rest : List PanicEntry}
    {ch : Choices} {r : Config × Store × Choices × StepLabel}
    (hx : stepPanicStop a s first rest ch = .ok r) : stepPanicStop b s first rest ch = .ok r := by
  unfold stepPanicStop at hx ⊢
  split at hx
  · simp only [bind_eq_ok] at hx
    obtain ⟨msg, -, hx⟩ := hx
    simp [throw, throwThe, MonadExceptOf.throw] at hx
  · split at hx
    · simp only [bind_eq_ok] at hx ⊢
      obtain ⟨m, hm, hx⟩ := hx
      exact ⟨m, h.phaseMark_mono hm, hx⟩
    · exact hx
    · simp [throw, throwThe, MonadExceptOf.throw] at hx

end ProgramCtx.SubTables

/-! ## §5 The lift: one step, then runs

`stepFn` reads the context only through the helpers of §3/§4 (its body passes `ctx` to 23
helpers at 27 sites, the lane's scan). The step lemma is one `fun_cases` sweep over the step's
arms with ONE leaf tactic: unfold the whole's arm, rewrite the slice's arm through every
equality of §3, and close by identity — or, at the positions that read a record, by the
`Passes`-guarded equalities of §4a through the `toResult` bind (the strict apply, its pick-holding
twin, the comma-ok apply), by the `.stop` arm's success-preservation (`stepPanicStop_mono`: the
decision step, the phase step), or, at the seven frame-entry positions and the two step helpers
that enter frames, by the success-preservation of §4b through the bind. The raise arm is
table-free since 2026-10-23 (`panicEntryOf` takes no context) and closes by identity. The two arms
below are the feasibility checkpoint's hand proofs (the declared call and the last-argument
entry), kept as the record of the shape; `stepFn_mono` subsumes them. -/

namespace TableMono
/-- A successful bind whose first action is preserved is preserved. -/
theorem bind_ok_mono {α β : Type} {x y : Except Stop α} (hxy : ∀ v, x = .ok v → y = .ok v)
    (k : α → Except Stop β) {r : β} (hx : x >>= k = .ok r) : y >>= k = .ok r := by
  cases hx' : x with
  | error e => rw [hx'] at hx; simp [Bind.bind, Except.bind] at hx
  | ok v => rw [hxy v hx']; rw [hx'] at hx; exact hx
end TableMono

namespace ProgramCtx.SubTables
variable {a b : ProgramCtx}

/-! ### Checkpoint arm A: the declared call statement (argument walk, or the nullary entry) -/
theorem exec_call_mono (h : a.SubTables b) {s : Store} {targets : Array Assignee} {fid : FuncId}
    {args : Array Expr} {env : LocalEnv} {k : Cont} {ch : Choices}
    {r : Config × Store × Choices × StepLabel}
    (hx : stepFn a s (.exec (.call targets fid args) env k) ch = .ok r) :
    stepFn b s (.exec (.call targets fid args) env k) ch = .ok r := by
  have hf := h.tablesFree_eq
  simp only [stepFn] at hx ⊢
  cases hp : targetsPlan targets.toList with
  | none => rw [hp] at hx; simp [throw, throwThe, MonadExceptOf.throw] at hx
  | some plans =>
    rw [hp] at hx; dsimp only at hx ⊢
    cases hargs : args.toList with
    | cons e rest => rw [hargs] at hx; dsimp only at hx ⊢; exact hx
    | nil =>
      rw [hargs] at hx; dsimp only at hx ⊢
      exact bind_ok_mono (fun _ he => h.enterFramePickV_mono he) _ hx

/-! ### Checkpoint arm B: the last argument delivered — the entry (dynamic dispatch inside) -/
theorem retV_callArgsK_mono (h : a.SubTables b) {s : Store} {v : GoValue} {fid : FuncId}
    {plans : List (TargetShape × List Expr)} {vals : List GoValue} {pending : List Expr}
    {env : LocalEnv} {k' : Cont} {ch : Choices} {r : Config × Store × Choices × StepLabel}
    (hx : stepFn a s (.retV v (.callArgsK fid plans vals pending env k')) ch = .ok r) :
    stepFn b s (.retV v (.callArgsK fid plans vals pending env k')) ch = .ok r := by
  simp only [stepFn] at hx ⊢
  cases pending with
  | cons e rest => exact hx
  | nil => exact bind_ok_mono (fun _ he => h.enterFramePickV_mono he) _ hx

/-! ### The sweep: every arm by one leaf tactic (the measurement) -/
theorem stepFn_mono (h : a.SubTables b) {s : Store} {c : Config} {ch : Choices}
    {r : Config × Store × Choices × StepLabel} (hx : stepFn a s c ch = .ok r) :
    stepFn b s c ch = .ok r := by
  have hf := h.tablesFree_eq
  revert hx
  fun_cases stepFn a s c ch
  all_goals (try simp only [stepFn, *])
  all_goals intro hx
  all_goals (try free_rw_at hf hx)
  all_goals (try free_rw hf)
  all_goals (try exact hx)
  all_goals (try exact bind_ok_mono (fun _ he => h.enterFramePickV_mono he) _ hx)
  all_goals (try exact bind_toResult_mono (fun hp => h.applyStrictOp_eq hp) hx)
  all_goals (try exact bind_toResult_mono (fun hp => h.applyStrictOpPick_eq hp) hx)
  all_goals (try exact bind_toResult_mono (fun hp => h.applyRhsOp_eq hp) hx)
  all_goals (try exact h.stepFrameExit_mono hx)
  all_goals (try exact h.stepNextOther_mono hx)
  all_goals (try exact h.stepPanicStop_mono hx)
  all_goals (try (split <;> simp_all))

/-! ### The lift to runs -/

/-- **G16, the `Prefix` form**: a labelled run under a slice is the same run under the whole. -/
theorem prefix_mono (h : a.SubTables b) {n : Nat} {s sf : Store} {c cf : Config} {ch chf : Choices}
    {ls : List StepLabel} (hp : Prefix a n s c ch ls sf cf chf) : Prefix b n s c ch ls sf cf chf := by
  induction hp with
  | done => exact .done
  | step hs _ ih => exact .step (h.stepFn_mono hs) ih

/-- An abort's finish is the same under the whole (the rendering reads the type table, the
displays and — for a defined-type payload — the slice's own record of its carrier). -/
theorem finish_aborted_mono (h : a.SubTables b) {s : Store} {c : Config} {ch ch'' : Choices}
    {rec : List PickRecord} {t : String}
    (hf : Finish a s c ch rec (.aborted t s ch'') 1) : Finish b s c ch rec (.aborted t s ch'') 1 := by
  cases hf with
  | aborted h1 h2 h3 => exact .aborted h1 h2 (h.abortMsg_mono h3)

/-- The sequential driver's normal completion under a slice completes identically under the whole. -/
theorem execStmtLoop_ok_mono (h : a.SubTables b) {fuel : Nat} {s sf : Store} {c : Config}
    {ch chf : Choices} (hr : execStmtLoop a fuel s c ch = .ok (sf, chf)) :
    execStmtLoop b fuel s c ch = .ok (sf, chf) := by
  obtain ⟨n, hn, ls, hp⟩ := (run_ok_iff a fuel s sf c ch chf).mp hr
  exact (run_ok_iff b fuel s sf c ch chf).mpr ⟨n, hn, ls, h.prefix_mono hp⟩

/-- The sequential driver's Go panic under a slice is the same panic under the whole. -/
theorem execStmtLoop_panic_mono (h : a.SubTables b) {fuel : Nat} {s : Store} {c : Config}
    {ch : Choices} {t : String} (hr : execStmtLoop a fuel s c ch = .error (.terminal (.panic t))) :
    execStmtLoop b fuel s c ch = .error (.terminal (.panic t)) := by
  obtain ⟨n, ls, sf, cf, chf, ch'', rec, hn, hp, hfin⟩ := (run_panic_iff a fuel s c ch t).mp hr
  exact (run_panic_iff b fuel s c ch t).mpr
    ⟨n, ls, sf, cf, chf, ch'', rec, hn, h.prefix_mono hp, h.finish_aborted_mono hfin⟩

end ProgramCtx.SubTables

end GoLean.GoCore
