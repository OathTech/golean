import GoLean.GoCore.Syntax

/-! Complete syntactic collection of `Ty.defined` indices. This is deliberately
different from `Ty.deps`: references under pointers, function signatures and
other indirections still require a table entry, although they contribute no
edge to the well-founded runtime resolution order. No constructor catch-all
is used in these traversals. Adding syntax requires choosing its traversal.
-/
namespace GoLean.GoCore.Admission

mutual
def tyIndices : Ty → List TypeIdx
  | .bool | .int _ | .float _ | .string | .interface _ | .unsupported _ | .sync _ => []
  | .defined i => [i]
  | .array _ t | .slice t | .pointer t | .chan _ t => tyIndices t
  | .map k v => tyIndices k ++ tyIndices v
  | .funcType ps rs _ => tyListIndices ps ++ tyListIndices rs
def tyListIndices : List Ty → List TypeIdx
  | [] => []
  | t :: ts => tyIndices t ++ tyListIndices ts
end

def optTyIndices (t : Option Ty) : List TypeIdx := t.toList.flatMap tyIndices
def paramIndices (p : Param) : List TypeIdx := tyIndices p.typ
def paramsIndices (ps : Array Param) : List TypeIdx := ps.toList.flatMap paramIndices
def typeDefIndices : TypeDef → List TypeIdx
  | .struct fs => fs.toList.flatMap (fun f => tyIndices f.typ)
  | .interfaceDef ms => ms.toList.flatMap fun m =>
      tyListIndices m.params.toList ++ tyListIndices m.results.toList
  | .defined t => tyIndices t
  | .opaqueDecl _ => []

mutual
def exprIndices : Expr → List TypeIdx
  | .var _ | .intLit _ _ | .floatLit _ _ _ | .stringLit _ | .boolLit _
  | .ref _ | .global _ | .recoverCall | .unsupported _ => []
  | .nil t => optTyIndices t
  | .convert t e | .deref e t => tyIndices t ++ exprIndices e
  | .bytesFromString e | .stringFromByteSlice e | .stringFromRune e
  | .bitNeg e | .neg e | .not e | .addrOfDeref e | .runesFromString e
  | .stringFromRuneSlice e | .floatBits _ e => exprIndices e
  | .add l r | .sub l r | .mul l r | .div l r | .mod l r
  | .shiftLeft l r | .shiftRight l r | .bitAnd l r | .bitOr l r
  | .bitXor l r | .bitClear l r | .atMostCmp l r | .atLeastCmp l r
  | .lessCmp l r | .greaterCmp l r | .and l r | .or l r
  | .indexGet l r | .indexAddr l r | .runeAt l r | .runeSizeAt l r =>
      exprIndices l ++ exprIndices r
  | .eqCmp t l r | .neqCmp t l r => tyIndices t ++ exprIndices l ++ exprIndices r
  | .funcVal _ es | .minOf es | .maxOf es => exprListIndices es.toList
  | .structLit t es => tyIndices t ++ exprListIndices es.toList
  | .fieldGet e _ _ | .fieldAddr e _ _ => exprIndices e
  | .arrayLit _ t es => tyIndices t ++ keyedExprIndices es.toList
  | .defaultValue t => tyIndices t
  | .toInterface t d e => tyIndices t ++ tyIndices d ++ exprIndices e
  | .typeAssert e t source => exprIndices e ++ tyIndices t ++ optTyIndices source
  | .mapGet b i k v => exprIndices b ++ exprIndices i ++ tyIndices k ++ tyIndices v
  | .slice b l h m => exprIndices b ++ exprIndices l ++ exprIndices h ++ optExprIndices m
  | .length e t | .capacity e t => exprIndices e ++ optTyIndices t
def exprListIndices : List Expr → List TypeIdx
  | [] => []
  | e :: es => exprIndices e ++ exprListIndices es
def keyedExprIndices : List (Int × Expr) → List TypeIdx
  | [] => []
  | (_, e) :: es => exprIndices e ++ keyedExprIndices es
def optExprIndices : Option Expr → List TypeIdx
  | none => []
  | some e => exprIndices e
end

def assigneeIndices : Assignee → List TypeIdx
  | .var _ | .unsupported _ => []
  | .addr e => exprIndices e
  | .mapElem b i k v => exprIndices b ++ exprIndices i ++ tyIndices k ++ tyIndices v
def assigneesIndices (as : Array Assignee) : List TypeIdx :=
  as.toList.flatMap assigneeIndices
def selectHeadIndices : SelectClauseHead → List TypeIdx
  | .send c v t => exprIndices c ++ exprIndices v ++ tyIndices t
  | .recv as c t => assigneesIndices as ++ exprIndices c ++ tyIndices t

mutual
def stmtIndices : Stmt → List TypeIdx
  | .seqn ss => stmtListIndices ss.toList
  | .block ps ss => paramsIndices ps ++ stmtListIndices ss.toList
  | .breakable s | .labeled _ s => stmtIndices s
  | .initialization p => paramIndices p
  | .assign a e => assigneeIndices a ++ exprIndices e
  | .assignMany as es | .call as _ es | .syncStmt _ es as | .atomicStmt _ _ es as =>
      assigneesIndices as ++ exprListIndices es.toList
  | .allocNew a e t => assigneeIndices a ++ exprIndices e ++ tyIndices t
  | .makeSlice a t e cap =>
      assigneeIndices a ++ tyIndices t ++ exprIndices e ++ optExprIndices cap
  | .makeMap a k v cap => assigneeIndices a ++ tyIndices k ++ tyIndices v ++ optExprIndices cap
  | .mapAssign b i e k v =>
      exprIndices b ++ exprIndices i ++ exprIndices e ++ tyIndices k ++ tyIndices v
  | .mapDelete b i k => exprIndices b ++ exprIndices i ++ tyIndices k
  | .clearMap b | .closeChan b | .panicStmt b | .unseqProbe b => exprIndices b
  | .clearSlice b t | .sortSlice b t => exprIndices b ++ tyIndices t
  | .mapLookup a ok b i k v => assigneeIndices a ++ assigneeIndices ok ++
      exprIndices b ++ exprIndices i ++ tyIndices k ++ tyIndices v
  | .typeAssert a ok e t => assigneeIndices a ++ assigneeIndices ok ++ exprIndices e ++ tyIndices t
  | .appendSlice a t s es => assigneeIndices a ++ tyIndices t ++ exprIndices s ++ exprIndices es
  | .copySlice a d s => assigneeIndices a ++ exprIndices d ++ exprIndices s
  | .callValue as e es => assigneesIndices as ++ exprIndices e ++ exprListIndices es.toList
  | .deferCall e es | .goStmt e es => exprIndices e ++ exprListIndices es.toList
  | .ifThenElse e t f => exprIndices e ++ stmtIndices t ++ stmtIndices f
  | .while e s => exprIndices e ++ stmtIndices s
  | .mapRange _ _ e k v s => exprIndices e ++ tyIndices k ++ tyIndices v ++ stmtIndices s
  | .returnStmt | .breakStmt | .continueStmt | .breakTo _ | .continueTo _
  | .inertLabel _ | .unsupported _ => []
  | .makeChan a t cap => assigneeIndices a ++ tyIndices t ++ optExprIndices cap
  | .chanSend c v t => exprIndices c ++ exprIndices v ++ tyIndices t
  | .chanRecv as c t => assigneesIndices as ++ exprIndices c ++ tyIndices t
  | .selectStmt cs d => selectIndices cs.toList ++ optStmtIndices d
  | .print _ es => exprListIndices es.toList
def stmtListIndices : List Stmt → List TypeIdx
  | [] => []
  | s :: ss => stmtIndices s ++ stmtListIndices ss
def selectIndices : List (SelectClauseHead × Stmt) → List TypeIdx
  | [] => []
  | (c, s) :: cs => selectHeadIndices c ++ stmtIndices s ++ selectIndices cs
def optStmtIndices : Option Stmt → List TypeIdx
  | none => []
  | some s => stmtIndices s
end

def programIndices (p : Program) : List TypeIdx :=
  p.typeDefs.toList.flatMap (fun t => typeDefIndices t.2) ++
  p.funcs.toList.flatMap (fun f => paramsIndices f.args ++ paramsIndices f.results ++ stmtIndices f.body) ++
  p.methods.toList.flatMap (fun m => tyIndices m.recv) ++
  p.globals.toList.flatMap (fun g => tyIndices g.typ)

/-- Exactly the property checked here: every collected `Ty.defined` has an
entry. This does not check `TypeId` or `FuncId` references, or well-typing. -/
def IndicesBound (p : Program) : Prop := ∀ i ∈ programIndices p, i < p.typeDefs.size

instance (p : Program) : Decidable (IndicesBound p) :=
  inferInstanceAs (Decidable (∀ i ∈ programIndices p, i < p.typeDefs.size))

end GoLean.GoCore.Admission
