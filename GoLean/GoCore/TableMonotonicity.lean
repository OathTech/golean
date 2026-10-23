import GoLean.GoCore.Prefix
import GoLean.GoCore.StateEqb

/-!
# Table monotonicity — a step under a SLICE of the tables is the step under the WHOLE (raft-proofs G16)

[AGENT lane core/g16-table-monotonicity-1023], 2026-10-23, on the [USER] ruling of 2026-10-23
(backlog row 48: go ahead with G16, urgent; the ask is
`~/projects/raft-proofs/docs/2026-10-23_golean-ask-table-monotonicity.md`).

The customer proves each raft function against a slice of the pinned wire — the function's
static call closure — and transfers the slice theorems to the whole program with ONE lemma:
a successful `stepFn` step under a context agrees with the step under any context that has the
SAME `typeDefs`, `globals`, `typeDisplays` (derived from `typeDefs`) and `methodSets`, and whose
`funcs`, `methods` and `promotions` CONTAIN the slice's rows (`ProgramCtx.SubTables`,
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
`validatePromotion` re-checks — but THIS module proves nothing about the decoder: the facts are
PREMISES of the relation, decidable on the whole program, and a consumer discharges them once
per wire.

## Why three CLOSURE conditions on the slice (and not fewer)

A successful step makes positive lookups only where a negative answer is a REFUSAL — dispatch
through `dynamicMethodSetRecorded`, a missing callee, a missing dispatch target. But three
readers turn a NEGATIVE table answer into a VALUE (the audit of every `ctx.functions`/
`ctx.methods`/`ctx.promotions`/`ctx.methodSets` read in `Ops.lean`/`Machine.lean`, 2026-10-23):

* `rewriteMark` (the panic chain entry's preprint mark, decided at the raise): `Error()`/
  `String()` are resolved on the payload's dynamic type and an absent method is a definite
  «no» — so the slice must keep every `Error`/`String` method the whole has, with its `Func`
  (`SliceClosed.reqMethod`/`reqPromotion`, the two members are in `requiredMembers`);
* `satisfiesMethodSig` (interface satisfaction for a type assertion / comma-ok / type switch
  against an interface declared in the type table): with the carrier's method-set record
  present — and `methodSets` is kept WHOLE here — a missing requirement is the definite
  «missing method N» answer; so the slice must keep every method and promotion whose member
  is a requirement of some declared interface, with its `Func` (same two fields);
* `pointerMethodSetNonEmpty` (whether `*T` has a method set, for gc's `pkgpath()` in the
  type-assertion panic text): an `any` over the method table, `false` from absence — so the
  slice must keep at least one method per receiver base the whole has (`SliceClosed.receivers`).

And one coupling: `dynamicDispatch?` treats a `Func` with no `MethodInfo` as a plain function,
so a kept `Func` keeps its `MethodInfo` (`SliceClosed.methodOfFunc`; a decoded wire carries the
two as one `program.methods[i]` entry, so a slice decoded from the wire has this for free).

`methodSets` is kept WHOLE (records are `(key, coverage)` pairs; the decoder cross-checks
nothing against them): `dynamicMethodSetRecorded` is read at the raise (`rewriteMark`'s
`.unrecorded` arm) on an arbitrary payload type, where a dropped record changes the chain entry.

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

/-- The member identities whose resolution the machine turns into a VALUE from a negative
answer: the two preprint members (`error`'s `Error`, `fmt.Stringer`'s `String`, consulted at
every raise of a boxed payload, `rewriteMark`) and every requirement of every interface
declared in the type table (consulted by satisfaction, `firstUnsatisfiedMethod?`). -/
def ProgramCtx.requiredMembers (c : ProgramCtx) : List Declaration.MemberId :=
  errorMember :: stringerMember ::
    c.types.toList.flatMap fun e =>
      match e.2 with
      | .interfaceDef sigs => sigs.toList.map (·.id)
      | _ => []

/-- The whole program's KEY DISCIPLINE: what makes each first-match lookup's answer the
unique row of its key, and keeps `resolveMethod?`'s arms disjoint. Every clause is a decidable
fact about the whole program alone. On a decoded wire they hold: the decoder refuses duplicate
function ids (hence duplicate method func-ids and, through `methodReceiverAgrees`, duplicate
(receiver, member) declarations), duplicate promotion keys, an empty promotion path and a
record naming a member its carrier declares (`NativeToIR.lean`, `validatePromotion`); a member
declared on both `T` and `*T` is rejected by `go/types` before a wire exists; and no frontend
`Func` carries a method-expression id it does not own. This module proves none of that — the
clauses are PREMISES, discharged once per wire by its consumer. -/
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

/-- The slice's CLOSURE under the whole: the rows whose ABSENCE the machine would read as an
answer (module header). Each clause is decidable on the pair. -/
structure ProgramCtx.SliceClosed (a b : ProgramCtx) : Prop where
  /-- A kept `Func` keeps its `MethodInfo` (`dynamicDispatch?` dispatches a method and runs a
  plain function by this table alone). -/
  methodOfFunc : ∀ m ∈ b.methods.toList, (∃ f ∈ a.functions.toList, f.id = m.funcId) →
    m ∈ a.methods.toList
  /-- Every method named by a required member is kept, with its `Func` (its signature is
  compared). -/
  reqMethod : ∀ m ∈ b.methods.toList, m.id ∈ b.requiredMembers →
    m ∈ a.methods.toList ∧ ∀ f ∈ b.functions.toList, f.id = m.funcId → f ∈ a.functions.toList
  /-- Every promotion record of a required member is kept, with its target's `Func`. -/
  reqPromotion : ∀ p ∈ b.promotions.toList, p.member ∈ b.requiredMembers →
    p ∈ a.promotions.toList ∧
      ∀ f, p.target = .method f → ∀ g ∈ b.functions.toList, g.id = f → g ∈ a.functions.toList
  /-- A receiver base with a method in the whole has one in the slice
  (`pointerMethodSetNonEmpty`). -/
  receivers : ∀ t, pointerMethodSetNonEmpty b t = true → pointerMethodSetNonEmpty a t = true

/-- **The sub-table relation** (G16): `a` is a slice of `b` — the same type table, globals,
displays and method-set records; `funcs`, `methods` and `promotions` sublists (filters: order
kept) of `b`'s; `b` key-disciplined; `a` closed under `b`. -/
structure ProgramCtx.SubTables (a b : ProgramCtx) : Prop where
  types : a.types = b.types
  globals : a.globals = b.globals
  typeDisplays : a.typeDisplays = b.typeDisplays
  methodSets : a.methodSets = b.methodSets
  functions : a.functions.toList.Sublist b.functions.toList
  methods : a.methods.toList.Sublist b.methods.toList
  promotions : a.promotions.toList.Sublist b.promotions.toList
  keyed : b.TablesKeyed
  closed : a.SliceClosed b

namespace ProgramCtx.SubTables

variable {a b : ProgramCtx}

theorem tablesFree_eq (h : a.SubTables b) : a.tablesFree = b.tablesFree := by
  simp only [ProgramCtx.tablesFree, h.types, h.globals, h.typeDisplays]

theorem requiredMembers_eq (h : a.SubTables b) : a.requiredMembers = b.requiredMembers := by
  simp only [ProgramCtx.requiredMembers, h.types]

theorem mem_functions (h : a.SubTables b) {f : Func} (hf : f ∈ a.functions.toList) :
    f ∈ b.functions.toList := h.functions.subset hf
theorem mem_methods (h : a.SubTables b) {m : MethodInfo} (hm : m ∈ a.methods.toList) :
    m ∈ b.methods.toList := h.methods.subset hm
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

/-- `methodSetCoverage?` agrees everywhere: the records are the same. -/
theorem methodSetCoverage?_eq (h : a.SubTables b) (key : String) :
    methodSetCoverage? a key = methodSetCoverage? b key := by
  rw [methodSetCoverage?_eq_find?, methodSetCoverage?_eq_find?, h.methodSets]

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

§4a: the readers that AGREE on the two contexts — everywhere (`methodSetCoverage?`: the records
are the same), or under the closures (`pointerMethodSetNonEmpty`; the resolution and signature
of every REQUIRED member; hence satisfaction, the type-assertion texts, the raise's preprint
mark and the abort rendering). §4b: the frame-entry family, which only PRESERVES a success —
a slice refuses where the whole dispatches (`callee?`, `promotedCallee`, `dynamicDispatch?`,
`enterFrame.plan`, `enterFramePickV`, and the two step helpers that enter frames). -/

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

namespace ProgramCtx.SubTables
variable {a b : ProgramCtx}

/-! ### Readers equal everywhere: the records are the same -/

theorem methodSetCoverage?_fun_eq (h : a.SubTables b) :
    @methodSetCoverage? a = @methodSetCoverage? b := funext h.methodSetCoverage?_eq

theorem dynamicMethodSetRecorded_eq (h : a.SubTables b) :
    @dynamicMethodSetRecorded a = @dynamicMethodSetRecorded b := by
  delta dynamicMethodSetRecorded
  simp only [methodCarrierKey?_eq h.tablesFree_eq, h.methodSetCoverage?_fun_eq]

theorem dynamicMethodSetExportedOnly_eq (h : a.SubTables b) :
    @dynamicMethodSetExportedOnly a = @dynamicMethodSetExportedOnly b := by
  delta dynamicMethodSetExportedOnly
  simp only [methodCarrierKey?_eq h.tablesFree_eq, h.methodSetCoverage?_fun_eq]

/-! ### `pointerMethodSetNonEmpty`: the slice keeps a method per receiver base (closure) -/

theorem pointerMethodSetNonEmpty_sub (h : a.SubTables b) {t : Ty}
    (ha : pointerMethodSetNonEmpty a t = true) : pointerMethodSetNonEmpty b t = true := by
  unfold pointerMethodSetNonEmpty at ha ⊢
  rw [← Array.any_toList, List.any_eq_true] at ha ⊢
  obtain ⟨m, hm, hp⟩ := ha
  exact ⟨m, h.mem_methods hm, hp⟩

theorem pointerMethodSetNonEmpty_eq (h : a.SubTables b) :
    @pointerMethodSetNonEmpty a = @pointerMethodSetNonEmpty b := by
  funext t
  rw [Bool.eq_iff_iff]
  exact ⟨h.pointerMethodSetNonEmpty_sub, h.closed.receivers t⟩

/-! ### The required members: resolution and signatures agree (closure) -/

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

theorem methodDecl?_eq_of_req (h : a.SubTables b) {M : Declaration.MemberId}
    (hM : M ∈ b.requiredMembers) (t : Ty) : methodDecl? a t M = methodDecl? b t M := by
  cases hb : methodDecl? b t M with
  | none =>
    cases ha : methodDecl? a t M with
    | none => rfl
    | some m => have := h.methodDecl?_mono ha; rw [hb] at this; cases this
  | some m =>
    obtain ⟨h1, h2, h3⟩ := methodDecl?_some hb
    have hmb : m ∈ b.methods.toList := by simpa using h3
    have hma : m ∈ a.methods.toList :=
      (h.closed.reqMethod m hmb (MemberId.beq_sound h1 ▸ hM)).1
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

theorem promotion?_eq_of_req (h : a.SubTables b) {M : Declaration.MemberId}
    (hM : M ∈ b.requiredMembers) (c : TypeId) : promotion? a c M = promotion? b c M := by
  cases hb : promotion? b c M with
  | none =>
    cases ha : promotion? a c M with
    | none => rfl
    | some p => have := h.promotion?_mono ha; rw [hb] at this; cases this
  | some p =>
    obtain ⟨h1, h2, h3⟩ := promotion?_some hb
    have hpb : p ∈ b.promotions.toList := by simpa using h3
    have hpa : p ∈ a.promotions.toList :=
      (h.closed.reqPromotion p hpb (MemberId.beq_sound h2 ▸ hM)).1
    obtain ⟨p', hp'⟩ : ∃ p', promotion? a c M = some p' := by
      rw [promotion?_eq_find?]
      cases hfa : a.promotions.toList.find? (fun q => q.type == c && q.member == M) with
      | some p' => exact ⟨p', rfl⟩
      | none =>
        exact absurd (by simp only [Bool.and_eq_true, beq_iff_eq]; exact ⟨h1, h2⟩)
          (List.find?_eq_none.mp hfa p hpa)
    have := h.promotion?_mono hp'
    rw [hb] at this
    rw [hp']; exact this.symm

theorem resolvePromoted?_eq_of_req (h : a.SubTables b) {M : Declaration.MemberId}
    (hM : M ∈ b.requiredMembers) (base : Ty) (ptr : Bool) :
    resolvePromoted? a base ptr M = resolvePromoted? b base ptr M := by
  delta resolvePromoted?
  simp only [types_eq h.tablesFree_eq, h.promotion?_eq_of_req hM]

theorem resolveMethod?_eq_of_req (h : a.SubTables b) {M : Declaration.MemberId}
    (hM : M ∈ b.requiredMembers) (t : Ty) : resolveMethod? a t M = resolveMethod? b t M := by
  delta resolveMethod?
  simp only [h.methodDecl?_eq_of_req hM, h.resolvePromoted?_eq_of_req hM]

end ProgramCtx.SubTables

/-- Where a resolution's callable target comes from: a declared method's own `funcId` (no stub
signature) or a promotion record's target and signature. -/
theorem resolveMethod?_target {ctx : ProgramCtx} {t : Ty} {M : Declaration.MemberId}
    {r : MethodResolution} (hr : resolveMethod? ctx t M = some r) :
    (∃ m ∈ ctx.methods.toList, m.id = M ∧ r.target = .method m.funcId ∧ r.sig = none) ∨
    (∃ p ∈ ctx.promotions.toList, p.member = M ∧ r.target = p.target ∧ r.sig = p.sig) := by
  have hprom : ∀ {base : Ty} {ptr : Bool}, resolvePromoted? ctx base ptr M = some r →
      ∃ p ∈ ctx.promotions.toList, p.member = M ∧ r.target = p.target ∧ r.sig = p.sig := by
    intro base ptr hp
    unfold resolvePromoted? at hp
    split at hp
    · split at hp
      · split at hp
        · split at hp
          · cases hp
          · obtain ⟨-, h2, h3⟩ := promotion?_some ‹_›
            cases hp
            exact ⟨_, by simpa using h3, MemberId.beq_sound h2, rfl, rfl⟩
        · cases hp
      · cases hp
    · cases hp
  unfold resolveMethod? at hr
  split at hr
  · obtain ⟨h1, -, h3⟩ := methodDecl?_some ‹_›
    cases hr
    exact .inl ⟨_, by simpa using h3, MemberId.beq_sound h1, rfl, rfl⟩
  · split at hr
    · cases hr
    · cases hr
    · split at hr
      · obtain ⟨h1, -, h3⟩ := methodDecl?_some ‹_›
        cases hr
        exact .inl ⟨_, by simpa using h3, MemberId.beq_sound h1, rfl, rfl⟩
      · exact .inr (hprom hr)
    · exact .inr (hprom hr)

namespace ProgramCtx.SubTables
variable {a b : ProgramCtx}

theorem resolvedSignature?_eq_of_req (h : a.SubTables b) {M : Declaration.MemberId}
    (hM : M ∈ b.requiredMembers) {t : Ty} {r : MethodResolution}
    (hr : resolveMethod? b t M = some r) :
    resolvedSignature? a M r = resolvedSignature? b M r := by
  delta resolvedSignature?
  simp only [interfaceDeclaredMethods?_eq h.tablesFree_eq]
  rcases resolveMethod?_target hr with ⟨m, hm, rfl, ht, hs⟩ | ⟨p, hp, rfl, ht, hs⟩
  · rw [hs, ht]
    exact h.funcSignature?_eq_of_kept (h.closed.reqMethod m hm hM).2
  · rw [hs, ht]
    cases p.sig with
    | some sg => rfl
    | none =>
      cases hpt : p.target with
      | method f => exact h.funcSignature?_eq_of_kept ((h.closed.reqPromotion p hp hM).2 f hpt)
      | iface i => rfl

theorem satisfiesMethodSig_eq (h : a.SubTables b) {req : MethodSig}
    (hreq : req.id ∈ b.requiredMembers) (t : Ty) :
    satisfiesMethodSig a t req = satisfiesMethodSig b t req := by
  delta satisfiesMethodSig
  rw [h.resolveMethod?_eq_of_req hreq]
  cases hr : resolveMethod? b t req.id with
  | none => rfl
  | some r => simp only [h.resolvedSignature?_eq_of_req hreq hr]

/-- A requirement of a declared interface is a required member. -/
theorem mem_requiredMembers_of_decl {ctx : ProgramCtx} {I : TypeId} {reqs : Array MethodSig}
    (hd : interfaceDeclaredMethods? ctx I = some reqs) {sg : MethodSig} (hs : sg ∈ reqs.toList) :
    sg.id ∈ ctx.requiredMembers := by
  unfold interfaceDeclaredMethods? at hd
  cases hl : ctx.types.lookupName? I with
  | none => rw [hl] at hd; cases hd
  | some e =>
    rw [hl] at hd
    obtain ⟨idx, d⟩ := e
    cases d with
    | interfaceDef ms =>
      simp only [Option.some.injEq] at hd
      subst hd
      unfold TypeEnv.lookupName? at hl
      obtain ⟨x, hx, hfx⟩ := List.exists_of_findSome?_eq_some hl
      have hmem : x.1 ∈ ctx.types.toList := List.fst_mem_of_mem_zipIdx hx
      split at hfx
      · simp only [Option.some.injEq, Prod.mk.injEq] at hfx
        unfold ProgramCtx.requiredMembers
        refine List.mem_cons_of_mem _ (List.mem_cons_of_mem _ ?_)
        rw [List.mem_flatMap]
        refine ⟨x.1, hmem, ?_⟩
        rw [hfx.2]
        simpa using List.mem_map_of_mem (f := MethodSig.id) hs
      · cases hfx
    | _ => cases hd

theorem firstUnsatisfiedMethod?_eq (h : a.SubTables b) (t : Ty) (I : TypeId) :
    firstUnsatisfiedMethod? a t I = firstUnsatisfiedMethod? b t I := by
  unfold firstUnsatisfiedMethod?
  simp only [interfaceDeclaredMethods?_eq h.tablesFree_eq, h.dynamicMethodSetRecorded_eq,
    h.dynamicMethodSetExportedOnly_eq, goTypeNameForMessage_eq h.tablesFree_eq]
  cases hd : interfaceDeclaredMethods? b I with
  | none => rfl
  | some reqs =>
    dsimp only
    congr 1
    congr 1
    rw [← Array.foldl_toList, ← Array.foldl_toList]
    apply foldl_ext'
    intro acc req hreq
    cases acc <;> simp only [h.satisfiesMethodSig_eq (mem_requiredMembers_of_decl hd hreq)]

theorem dynamicImplementsInterface_eq (h : a.SubTables b) :
    @dynamicImplementsInterface a = @dynamicImplementsInterface b := by
  funext t I; delta dynamicImplementsInterface; rw [h.firstUnsatisfiedMethod?_eq]

theorem typeAssertValue_eq (h : a.SubTables b) : @typeAssertValue a = @typeAssertValue b := by
  delta typeAssertValue
  simp only [h.dynamicImplementsInterface_eq, defaultValue_eq h.tablesFree_eq]

theorem applyRhsOp_eq (h : a.SubTables b) : @applyRhsOp a = @applyRhsOp b := by
  delta applyRhsOp
  have hf := h.tablesFree_eq
  simp only [h.typeAssertValue_eq]
  free_rw hf

theorem typePkgForMessage_eq (h : a.SubTables b) : @typePkgForMessage a = @typePkgForMessage b := by
  delta typePkgForMessage
  have hf := h.tablesFree_eq
  simp only [h.pointerMethodSetNonEmpty_eq, h.methodSetCoverage?_fun_eq]
  free_rw hf

theorem typeAssertPanicMessage_eq (h : a.SubTables b) :
    @typeAssertPanicMessage a = @typeAssertPanicMessage b := by
  delta typeAssertPanicMessage
  have hf := h.tablesFree_eq
  simp only [h.typePkgForMessage_eq]
  free_rw hf

theorem applyStrictOp_eq (h : a.SubTables b) : @applyStrictOp a = @applyStrictOp b := by
  delta applyStrictOp
  have hf := h.tablesFree_eq
  simp only [h.typeAssertValue_eq, h.firstUnsatisfiedMethod?_eq, h.typeAssertPanicMessage_eq]
  free_rw hf

theorem applyStrictOpPick_eq (h : a.SubTables b) : @applyStrictOpPick a = @applyStrictOpPick b := by
  delta applyStrictOpPick
  have hf := h.tablesFree_eq
  simp only [h.applyStrictOp_eq]
  free_rw hf

/-! ### The preprint members: resolved the same (closure), so the raise's mark and the abort
rendering agree -/

theorem errorMember_mem (b : ProgramCtx) : errorMember ∈ b.requiredMembers := by
  simp [ProgramCtx.requiredMembers]
theorem stringerMember_mem (b : ProgramCtx) : stringerMember ∈ b.requiredMembers := by
  simp [ProgramCtx.requiredMembers]

theorem hasNoArgStringMethod_eq (h : a.SubTables b) {M : Declaration.MemberId}
    (hM : M ∈ b.requiredMembers) (t : Ty) :
    hasNoArgStringMethod a t M = hasNoArgStringMethod b t M := by
  delta hasNoArgStringMethod
  rw [h.resolveMethod?_eq_of_req hM]
  cases hr : resolveMethod? b t M with
  | none => rfl
  | some r => simp only [h.resolvedSignature?_eq_of_req hM hr]

theorem panicPayloadIsRewritten_eq (h : a.SubTables b) :
    @panicPayloadIsRewritten a = @panicPayloadIsRewritten b := by
  funext t
  delta panicPayloadIsRewritten
  rw [h.hasNoArgStringMethod_eq (M := ⟨"Error", ""⟩) (errorMember_mem b),
    h.hasNoArgStringMethod_eq (M := ⟨"String", ""⟩) (stringerMember_mem b)]

theorem rewriteMark_eq (h : a.SubTables b) : @rewriteMark a = @rewriteMark b := by
  funext v
  delta rewriteMark
  cases v <;> simp only [h.hasNoArgStringMethod_eq (errorMember_mem b),
    h.hasNoArgStringMethod_eq (stringerMember_mem b), h.dynamicMethodSetRecorded_eq]

theorem panicEntryOf_eq (h : a.SubTables b) : @panicEntryOf a = @panicEntryOf b := by
  delta panicEntryOf; rw [h.rewriteMark_eq]

theorem renderPanicRewrite_eq (h : a.SubTables b) : @renderPanicRewrite a = @renderPanicRewrite b := by
  delta renderPanicRewrite
  have hf := h.tablesFree_eq
  simp only [h.dynamicMethodSetRecorded_eq, h.panicPayloadIsRewritten_eq]
  free_rw hf

theorem renderPanicPayload_eq (h : a.SubTables b) : @renderPanicPayload a = @renderPanicPayload b := by
  delta renderPanicPayload; simp only [h.renderPanicRewrite_eq]

theorem renderPanicHead_eq (h : a.SubTables b) : @renderPanicHead a = @renderPanicHead b := by
  delta renderPanicHead; simp only [h.renderPanicPayload_eq]

theorem abortMsg_eq (h : a.SubTables b) : @abortMsg a = @abortMsg b := by
  delta abortMsg
  simp only [h.renderPanicHead_eq, abortRefusal_eq h.tablesFree_eq]

theorem stepPanicStop_eq (h : a.SubTables b) : @stepPanicStop a = @stepPanicStop b := by
  delta stepPanicStop; simp only [h.abortMsg_eq]

end ProgramCtx.SubTables

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

/-! ## §5 The lift: one step, then runs

`stepFn` reads the context only through the helpers of §3/§4 (its body passes `ctx` to 23
helpers at 27 sites, the lane's scan). The step lemma is one `fun_cases` sweep over the 155
arms with ONE leaf tactic: unfold the whole's arm, rewrite the slice's arm through every
equality of §3/§4a, and close by identity — or, at the seven frame-entry positions and the
two step helpers that enter frames, by the success-preservation of §4b through the bind. The
two arms below are the feasibility checkpoint's hand proofs (the declared call and the
last-argument entry), kept as the record of the shape; `stepFn_mono` subsumes them. -/

/-- Rewrite every table-free helper (§3) and every reader that agrees (§4a) from the slice to
the whole, at the given locations. -/
macro "mono_rw" h:term:max hf:term:max : tactic =>
  `(tactic| simp only [TableMono.types_eq $hf, TableMono.typeDisplays_eq $hf, TableMono.globals_eq $hf, TableMono.structTagCompatible_eq $hf, TableMono.loadLoc_eq $hf, TableMono.Mem_load_eq $hf, TableMono.loadRoot_eq $hf, TableMono.Mem_loadBinding_eq $hf, TableMono.Mem_loadBindingFor_eq $hf, TableMono.Mem_loadElems_eq $hf, TableMono.Mem_loadFor_eq $hf, TableMono.Mem_loadRun_eq $hf, TableMono.Mem_loadSlice_eq $hf, TableMono.writeAt_eq $hf, TableMono.storeLoc_eq $hf, TableMono.Mem_store_eq $hf, TableMono.Mem_storeElems_eq $hf, TableMono.Mem_storeRun_eq $hf, TableMono.normalizeValueForTy_eq $hf, TableMono.Store_alloc_eq $hf, TableMono.typeDisplay?_eq $hf, TableMono.displayNameOfId_eq $hf, TableMono.displayNameOf_eq $hf, TableMono.goTypeNameForMessage_eq $hf, TableMono.payloadDynamicTypeNote_eq $hf, TableMono.abortRefusal_eq $hf, TableMono.methodCarrierKey?_eq $hf, TableMono.interfaceDeclaredMethods?_eq $hf, TableMono.defaultValue_eq $hf, TableMono.allocDecls_eq $hf, TableMono.atomicStore_eq $hf, TableMono.applyAtomicOp_eq $hf, TableMono.applyChanOp_eq $hf, TableMono.tyUncomparable_eq $hf, TableMono.valueHashability_eq $hf, TableMono.checkKeyHashable_eq $hf, TableMono.valueEq_eq $hf, TableMono.mapEntryIndex?_eq $hf, TableMono.mapLookupValue_eq $hf, TableMono.commitClause_eq $hf, TableMono.applySelectCore_eq $hf, TableMono.applySelect_eq $hf, TableMono.applySlice_eq $hf, TableMono.buildArrayValue_eq $hf, TableMono.buildDefaultArrayValue_eq $hf, TableMono.mapAssignValue_plan_eq $hf, TableMono.applyStmtOpCore_plan_eq $hf, TableMono.buildAppendBackingValue_eq $hf, TableMono.applyStmtOp_plan_eq $hf, TableMono.buildStructFields_eq $hf, TableMono.buildStructValue_eq $hf, TableMono.convertValueToTy_eq $hf, TableMono.indexTargetLoc_eq $hf, TableMono.dynamicTypeNameForMessage_eq $hf, TableMono.convCapApplyAt_eq $hf, TableMono.convCapApply_eq $hf, TableMono.syncCell_eq $hf, TableMono.applySyncOpCore_eq $hf, TableMono.applyTryLock_eq $hf, TableMono.applySyncOp_eq $hf, TableMono.bindIterVars_eq $hf, TableMono.bindParams_eq $hf, TableMono.structFieldValue_eq $hf, TableMono.promotionHop_eq $hf, TableMono.promotionWalk_eq $hf, TableMono.receiverAt_eq $hf, TableMono.symbolKeyForMessage_eq $hf, TableMono.loadResults_eq $hf, TableMono.mapIterCandidates_eq $hf, TableMono.preprintFatalStop_eq $hf, TableMono.panicUnwindStop_eq $hf, TableMono.projChainTarget_eq $hf, TableMono.resolveChain_eq $hf, TableMono.stepUnseqEnter_eq $hf, TableMono.unseqGuard_eq $hf, TableMono.unseqReadTarget_eq $hf, TableMono.unseqLoad_plan_eq $hf, TableMono.unseqStorePlan_eq $hf, TableMono.unseqAtom_eq $hf, TableMono.unseqAtoms_eq $hf, TableMono.unseqUnfrozenAnchor?_eq $hf, TableMono.unseqUnfrozenPlan?_eq $hf, TableMono.unseqTargetPlan_eq $hf, TableMono.stepUnseqNext_eq $hf, TableMono.stepUnseqValue_eq $hf, TableMono.storeTarget_plan_eq $hf, ProgramCtx.SubTables.applyStrictOp_eq $h,
      ProgramCtx.SubTables.applyStrictOpPick_eq $h, ProgramCtx.SubTables.applyRhsOp_eq $h,
      ProgramCtx.SubTables.stepPanicStop_eq $h, ProgramCtx.SubTables.panicEntryOf_eq $h])
macro "mono_rw" h:term:max hf:term:max "at" loc:ident : tactic =>
  `(tactic| simp only [TableMono.types_eq $hf, TableMono.typeDisplays_eq $hf, TableMono.globals_eq $hf, TableMono.structTagCompatible_eq $hf, TableMono.loadLoc_eq $hf, TableMono.Mem_load_eq $hf, TableMono.loadRoot_eq $hf, TableMono.Mem_loadBinding_eq $hf, TableMono.Mem_loadBindingFor_eq $hf, TableMono.Mem_loadElems_eq $hf, TableMono.Mem_loadFor_eq $hf, TableMono.Mem_loadRun_eq $hf, TableMono.Mem_loadSlice_eq $hf, TableMono.writeAt_eq $hf, TableMono.storeLoc_eq $hf, TableMono.Mem_store_eq $hf, TableMono.Mem_storeElems_eq $hf, TableMono.Mem_storeRun_eq $hf, TableMono.normalizeValueForTy_eq $hf, TableMono.Store_alloc_eq $hf, TableMono.typeDisplay?_eq $hf, TableMono.displayNameOfId_eq $hf, TableMono.displayNameOf_eq $hf, TableMono.goTypeNameForMessage_eq $hf, TableMono.payloadDynamicTypeNote_eq $hf, TableMono.abortRefusal_eq $hf, TableMono.methodCarrierKey?_eq $hf, TableMono.interfaceDeclaredMethods?_eq $hf, TableMono.defaultValue_eq $hf, TableMono.allocDecls_eq $hf, TableMono.atomicStore_eq $hf, TableMono.applyAtomicOp_eq $hf, TableMono.applyChanOp_eq $hf, TableMono.tyUncomparable_eq $hf, TableMono.valueHashability_eq $hf, TableMono.checkKeyHashable_eq $hf, TableMono.valueEq_eq $hf, TableMono.mapEntryIndex?_eq $hf, TableMono.mapLookupValue_eq $hf, TableMono.commitClause_eq $hf, TableMono.applySelectCore_eq $hf, TableMono.applySelect_eq $hf, TableMono.applySlice_eq $hf, TableMono.buildArrayValue_eq $hf, TableMono.buildDefaultArrayValue_eq $hf, TableMono.mapAssignValue_plan_eq $hf, TableMono.applyStmtOpCore_plan_eq $hf, TableMono.buildAppendBackingValue_eq $hf, TableMono.applyStmtOp_plan_eq $hf, TableMono.buildStructFields_eq $hf, TableMono.buildStructValue_eq $hf, TableMono.convertValueToTy_eq $hf, TableMono.indexTargetLoc_eq $hf, TableMono.dynamicTypeNameForMessage_eq $hf, TableMono.convCapApplyAt_eq $hf, TableMono.convCapApply_eq $hf, TableMono.syncCell_eq $hf, TableMono.applySyncOpCore_eq $hf, TableMono.applyTryLock_eq $hf, TableMono.applySyncOp_eq $hf, TableMono.bindIterVars_eq $hf, TableMono.bindParams_eq $hf, TableMono.structFieldValue_eq $hf, TableMono.promotionHop_eq $hf, TableMono.promotionWalk_eq $hf, TableMono.receiverAt_eq $hf, TableMono.symbolKeyForMessage_eq $hf, TableMono.loadResults_eq $hf, TableMono.mapIterCandidates_eq $hf, TableMono.preprintFatalStop_eq $hf, TableMono.panicUnwindStop_eq $hf, TableMono.projChainTarget_eq $hf, TableMono.resolveChain_eq $hf, TableMono.stepUnseqEnter_eq $hf, TableMono.unseqGuard_eq $hf, TableMono.unseqReadTarget_eq $hf, TableMono.unseqLoad_plan_eq $hf, TableMono.unseqStorePlan_eq $hf, TableMono.unseqAtom_eq $hf, TableMono.unseqAtoms_eq $hf, TableMono.unseqUnfrozenAnchor?_eq $hf, TableMono.unseqUnfrozenPlan?_eq $hf, TableMono.unseqTargetPlan_eq $hf, TableMono.stepUnseqNext_eq $hf, TableMono.stepUnseqValue_eq $hf, TableMono.storeTarget_plan_eq $hf, ProgramCtx.SubTables.applyStrictOp_eq $h,
      ProgramCtx.SubTables.applyStrictOpPick_eq $h, ProgramCtx.SubTables.applyRhsOp_eq $h,
      ProgramCtx.SubTables.stepPanicStop_eq $h, ProgramCtx.SubTables.panicEntryOf_eq $h] at $loc:ident)

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
  all_goals (try mono_rw h hf at hx)
  all_goals (try mono_rw h hf)
  all_goals (try exact hx)
  all_goals (try exact bind_ok_mono (fun _ he => h.enterFramePickV_mono he) _ hx)
  all_goals (try exact h.stepFrameExit_mono hx)
  all_goals (try exact h.stepNextOther_mono hx)
  all_goals (try (split <;> simp_all))

/-! ### The lift to runs -/

/-- **G16, the `Prefix` form**: a labelled run under a slice is the same run under the whole. -/
theorem prefix_mono (h : a.SubTables b) {n : Nat} {s sf : Store} {c cf : Config} {ch chf : Choices}
    {ls : List StepLabel} (hp : Prefix a n s c ch ls sf cf chf) : Prefix b n s c ch ls sf cf chf := by
  induction hp with
  | done => exact .done
  | step hs _ ih => exact .step (h.stepFn_mono hs) ih

/-- An abort's finish is the same under the whole (the rendering reads the type table, the
displays and the required members only). -/
theorem finish_aborted_mono (h : a.SubTables b) {s : Store} {c : Config} {ch ch'' : Choices}
    {rec : List PickRecord} {t : String}
    (hf : Finish a s c ch rec (.aborted t s ch'') 1) : Finish b s c ch rec (.aborted t s ch'') 1 := by
  cases hf with
  | aborted h1 h2 h3 => exact .aborted h1 h2 (h.abortMsg_eq ▸ h3)

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
