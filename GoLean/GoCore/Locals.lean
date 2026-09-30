import GoLean.GoCore.State
import GoLean.GoCore.Unseq

/-!
# Numeric locals: the name table's checked predicate and the env-lookup laws

B6 (window row 5, 2026-09-30; design note `docs/2026-09-30_numeric-locals-design.md`,
the logic team's request 3 of 2026-09-28). A local is a `VarId := Nat`, an index into
its function's name table `Func.locals`; the machine's `LocalEnv` walks scopes by id
exactly as it walked them by spelling. This module states, in the core and totally,
(i) which ids a function NAMES (`Func.ids`: its signature, its declarations, its
mentions), (ii) the decoder's final check `Func.localsOk` — checked in BOTH directions since the
fix round (the audit's F1, 2026-09-30): the table covers every named id, every table entry
is named, the signature's ids are pairwise distinct, and the entries' kinds agree with
where the ids occur — with the lemmas that turn a `localsOk` fact into «every id the
function names has a retained spelling» (`Func.localsOk_covers`), «no entry is dead»
(`localsOk_named`), and the kinds (`localsOk_argKind`/`_resultKind`/`_recvFirst`/`_bodyKind`), (iii) the two-line laws of `LocalEnv.declare` / `LocalEnv.lookup` a client composes
to read an activation's slots live beside `LocalEnv` in `State.lean`
(`LocalEnv.lookup_declare_self`/`_ne`, `lookup_pushScope`), and the frame-entry slot
lemmas (`bindParams_lookup`, `allocDecls_lookup`, `enterFrame_lookup_arg`/`_result`)
beside `enterFrame` in `Machine.lean`. Nothing here is read by `stepFn`.
-/

namespace GoLean.GoCore

mutual
/-- The declaration ids a statement DECLARES — block declarations, `.initialization`,
a `mapRange`'s variables, an `unseq` graph's cells — the complement of `Stmt.names`
(mentions). Total; no constructor catch-all (adding syntax requires choosing its
traversal — the `AdmissionIndices` discipline; the case list mirrors `Stmt.names`). -/
def Stmt.declIds : Stmt → List VarId
  | .seqn ss => stmtListDeclIds ss.toList
  | .block decls ss => decls.toList.map (·.id) ++ stmtListDeclIds ss.toList
  | .breakable s | .labeled _ s => Stmt.declIds s
  | .initialization p => [p.id]
  | .assign _ _ | .assignMany _ _ | .call _ _ _ | .syncStmt _ _ _ | .atomicStmt _ _ _ _
  | .allocNew _ _ _ | .makeSlice _ _ _ _ | .makeMap _ _ _ _ | .mapAssign _ _ _ _ _
  | .mapDelete _ _ _ | .clearMap _ | .closeChan _ | .panicStmt _ | .unseqProbe _
  | .clearSlice _ _ | .sortSlice _ _ | .mapLookup _ _ _ _ _ _ | .typeAssert _ _ _ _
  | .appendSlice _ _ _ _ | .copySlice _ _ _ | .callValue _ _ _ | .deferCall _ _ | .goStmt _ _
  | .returnStmt | .breakStmt | .continueStmt | .breakTo _ | .continueTo _
  | .inertLabel _ | .unsupported _ | .makeChan _ _ _ | .chanSend _ _ _ | .chanRecv _ _ _
  | .print _ _ => []
  | .unseq g t => g.cells.map (·.id)
      ++ g.occs.flatMap (fun o => o.body.valueBinds ++ o.body.targetBind?.toList) ++ Stmt.declIds t
  | .ifThenElse _ t f => Stmt.declIds t ++ Stmt.declIds f
  | .while _ s => Stmt.declIds s
  | .mapRange k v _ _ _ s => k.toList ++ v.toList ++ Stmt.declIds s
  | .selectStmt cs d => selectDeclIds cs.toList ++ optStmtDeclIds d
def stmtListDeclIds : List Stmt → List VarId
  | [] => []
  | s :: ss => Stmt.declIds s ++ stmtListDeclIds ss
def selectDeclIds : List (SelectClauseHead × Stmt) → List VarId
  | [] => []
  | (_, s) :: cs => Stmt.declIds s ++ selectDeclIds cs
def optStmtDeclIds : Option Stmt → List VarId
  | none => []
  | some s => Stmt.declIds s
end

/-- Every id a function NAMES: its signature's, then the body's declarations and its
mentions (`Stmt.names`, `Unseq.lean`). -/
def Func.ids (f : Func) : List VarId :=
  (f.args ++ f.results).toList.map (·.id) ++ f.body.declIds ++ f.body.names

/-- The signature's ids: the parameters (receiver and captures first), then the results. -/
def Func.sigIds (f : Func) : List VarId := (f.args ++ f.results).toList.map (·.id)

/-- The kind the table records for `id`, `none` past the table. -/
def Func.kindOf? (f : Func) (id : VarId) : Option LocalKind := (f.locals[id]?).map (·.kind)

/-- Tree ⊆ table: every id the function names has a table entry. -/
def Func.tableCovers (f : Func) : Bool := f.ids.all (· < f.locals.size)

/-- Table ⊆ tree (B6 fix round F1 (b), 2026-09-30): every table entry is declared or
referenced somewhere in the function — an entry nothing names is refused. -/
def Func.tableNamed (f : Func) : Bool := (List.range f.locals.size).all (f.ids.contains ·)

/-- The signature's ids are pairwise distinct (each parameter and result is its own slot —
`bindParams` binds each id to a fresh cell, so a repeat would silently shadow). -/
def Func.sigDistinct (f : Func) : Bool := namesDistinct f.sigIds

/-- A parameter's entry is the receiver, a parameter, a capture pointer, or a `$`-temporary
(a shim's / stub's synthesized parameter). (B6 fix round F1 (c).) -/
def Func.argKinds (f : Func) : Bool :=
  f.args.toList.all fun p =>
    match f.kindOf? p.id with
    | some .recv | some .param | some .capture | some .temp => true
    | _ => false

/-- A result's entry is a result or a `$`-temporary (an unnamed result's `$res{i}`). -/
def Func.resultKinds (f : Func) : Bool :=
  f.results.toList.all fun p =>
    match f.kindOf? p.id with
    | some .result | some .temp => true
    | _ => false

/-- Only the first parameter may be the receiver. -/
def Func.recvFirst (f : Func) : Bool :=
  (f.args.toList.drop 1).all fun p =>
    match f.kindOf? p.id with
    | some .recv => false
    | _ => true

/-- A local the BODY declares (a block declaration, an `.initialization`, a range variable, a
graph cell or binder) is a body local or a `$`-temporary — never a receiver, parameter,
capture or result (B6 fix round F1 (c): a body local cannot claim `recv`). -/
def Func.bodyKinds (f : Func) : Bool :=
  f.body.declIds.all fun id =>
    match f.kindOf? id with
    | some .local | some .temp => true
    | _ => false

/-- B6 c5 — the decoder's final, total check over a decoded function, checked in BOTH
directions since the fix round (2026-09-30, the audit's F1): the table covers every id the
tree names AND every table entry is named by the tree; the signature's ids are pairwise
distinct; the entries' KINDS agree with where the ids occur (receiver/parameter/capture/
temporary for a parameter — the receiver first —, result/temporary for a result,
local/temporary for a body declaration). `decodeProgram` refuses a function on which this
is `false`, naming the failing part; a consumer may `decide` it on a concrete program. -/
def Func.localsOk (f : Func) : Bool :=
  f.tableCovers && f.tableNamed && f.sigDistinct && f.argKinds && f.resultKinds
    && f.recvFirst && f.bodyKinds

theorem Func.localsOk_parts {f : Func} (h : f.localsOk = true) :
    f.tableCovers = true ∧ f.tableNamed = true ∧ f.sigDistinct = true ∧ f.argKinds = true
      ∧ f.resultKinds = true ∧ f.recvFirst = true ∧ f.bodyKinds = true := by
  unfold Func.localsOk at h
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1.1.1.1.1.1, h.1.1.1.1.1.2, h.1.1.1.1.2, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

/-- «Source spellings are retained» (request 3): under `localsOk`, every id the
function names has a table entry. -/
theorem Func.localsOk_covers {f : Func} (h : f.localsOk = true) {id : VarId}
    (hid : id ∈ f.ids) : (f.localName? id).isSome = true := by
  have hc := (Func.localsOk_parts h).1
  unfold Func.tableCovers at hc
  have hlt : id < f.locals.size := by
    have := List.all_eq_true.mp hc id hid
    simpa using this
  simp [Func.localName?, hlt]

/-- Table ⊆ tree: under `localsOk`, every table entry is named by the function (declared or
referenced) — no entry is dead metadata. -/
theorem Func.localsOk_named {f : Func} (h : f.localsOk = true) {i : Nat}
    (hi : i < f.locals.size) : i ∈ f.ids := by
  have hn := (Func.localsOk_parts h).2.1
  unfold Func.tableNamed at hn
  have := List.all_eq_true.mp hn i (List.mem_range.mpr hi)
  simpa using this

/-- Under `localsOk`, the signature's ids are pairwise distinct (the premise of the
frame-entry slot lemmas). -/
theorem Func.localsOk_sigDistinct {f : Func} (h : f.localsOk = true) :
    namesDistinct ((f.args ++ f.results).toList.map (·.id)) = true :=
  (Func.localsOk_parts h).2.2.1

/-- Under `localsOk`, a parameter's table kind is receiver, parameter, capture or temporary. -/
theorem Func.localsOk_argKind {f : Func} (h : f.localsOk = true) {p : Param}
    (hp : p ∈ f.args.toList) :
    f.kindOf? p.id = some .recv ∨ f.kindOf? p.id = some .param
      ∨ f.kindOf? p.id = some .capture ∨ f.kindOf? p.id = some .temp := by
  have ha := (Func.localsOk_parts h).2.2.2.1
  unfold Func.argKinds at ha
  have := List.all_eq_true.mp ha p hp
  cases hk : f.kindOf? p.id with
  | none => simp [hk] at this
  | some k => cases k <;> simp [hk] at this ⊢

/-- Under `localsOk`, a result's table kind is result or temporary. -/
theorem Func.localsOk_resultKind {f : Func} (h : f.localsOk = true) {p : Param}
    (hp : p ∈ f.results.toList) :
    f.kindOf? p.id = some .result ∨ f.kindOf? p.id = some .temp := by
  have hr := (Func.localsOk_parts h).2.2.2.2.1
  unfold Func.resultKinds at hr
  have := List.all_eq_true.mp hr p hp
  cases hk : f.kindOf? p.id with
  | none => simp [hk] at this
  | some k => cases k <;> simp [hk] at this ⊢

/-- Under `localsOk`, no parameter past the first is the receiver. -/
theorem Func.localsOk_recvFirst {f : Func} (h : f.localsOk = true) {p : Param}
    (hp : p ∈ f.args.toList.drop 1) : f.kindOf? p.id ≠ some .recv := by
  have hr := (Func.localsOk_parts h).2.2.2.2.2.1
  unfold Func.recvFirst at hr
  have := List.all_eq_true.mp hr p hp
  cases hk : f.kindOf? p.id with
  | none => simp
  | some k => cases k <;> simp [hk] at this ⊢

/-- Under `localsOk`, a body-declared id's table kind is local or temporary — a body local
cannot claim to be the receiver, a parameter, a capture or a result. -/
theorem Func.localsOk_bodyKind {f : Func} (h : f.localsOk = true) {id : VarId}
    (hid : id ∈ f.body.declIds) :
    f.kindOf? id = some .local ∨ f.kindOf? id = some .temp := by
  have hb := (Func.localsOk_parts h).2.2.2.2.2.2
  unfold Func.bodyKinds at hb
  have := List.all_eq_true.mp hb id hid
  cases hk : f.kindOf? id with
  | none => simp [hk] at this
  | some k => cases k <;> simp [hk] at this ⊢

end GoLean.GoCore
