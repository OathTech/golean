import GoLean.GoCore.State
import GoLean.GoCore.Unseq

/-!
# Numeric locals: the name table's checked predicate and the env-lookup laws

B6 (window row 5, 2026-09-30; design note `docs/2026-09-30_numeric-locals-design.md`,
the logic team's request 3 of 2026-09-28). A local is a `VarId := Nat`, an index into
its function's name table `Func.locals`; the machine's `LocalEnv` walks scopes by id
exactly as it walked them by spelling. This module states, in the core and totally,
(i) which ids a function NAMES (`Func.ids`: its signature, its declarations, its
mentions), (ii) the decoder's final check `Func.localsOk` — the table covers every
named id and the signature's ids are pairwise distinct — with the lemma that turns a
`localsOk` fact into «every id the function names has a retained spelling»
(`Func.localsOk_covers`), (iii) the two-line laws of `LocalEnv.declare` / `LocalEnv.lookup` a client composes
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
  | .unseq g t => g.cells.map (·.id) ++ Stmt.declIds t
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

/-- B6 c5 — the decoder's final, total check over a decoded function: its name table
covers every id it names, and the signature's ids are pairwise distinct (each
parameter and result is its own slot — `bindParams` binds each id to a fresh cell,
so a repeat would silently shadow). `decodeProgram` refuses a function on which
this is `false`; a consumer may `decide` it on a concrete program. -/
def Func.localsOk (f : Func) : Bool :=
  f.ids.all (· < f.locals.size) && namesDistinct ((f.args ++ f.results).toList.map (·.id))

/-- «Source spellings are retained» (request 3): under `localsOk`, every id the
function names has a table entry. -/
theorem Func.localsOk_covers {f : Func} (h : f.localsOk = true) {id : VarId}
    (hid : id ∈ f.ids) : (f.localName? id).isSome = true := by
  unfold Func.localsOk at h
  rw [Bool.and_eq_true] at h
  have hlt : id < f.locals.size := by
    have := List.all_eq_true.mp h.1 id hid
    simpa using this
  simp [Func.localName?, hlt]

/-- Under `localsOk`, the signature's ids are pairwise distinct (the premise of the
frame-entry slot lemmas). -/
theorem Func.localsOk_sigDistinct {f : Func} (h : f.localsOk = true) :
    namesDistinct ((f.args ++ f.results).toList.map (·.id)) = true := by
  unfold Func.localsOk at h
  rw [Bool.and_eq_true] at h
  exact h.2

end GoLean.GoCore
