import GoLean.GoCore.RecoveryAdmission
import GoLean.GoCore.Multi

namespace GoLean.GoCore.RecoveryTyping.Tests
open Machine

/-- Complete native artifact; the dedicated gate compares every field with fresh lowering. -/
def nativeRecovery : Program :=
{ typeDefs := #[({ key := "struct{}" }, GoLean.GoCore.TypeDef.struct #[]),
                ({ key := "$runtime.Error" },
                 GoLean.GoCore.TypeDef.opaqueDecl
                   "the machine's runtime-error payload type ($runtime.Error): structural use (==, normalization or conversion at the type, default value) is unmodeled — gc realizes several runtime.Error types behind one abort text (BUG-059 kind clause), so the machine refuses rather than answers")],
  funcs := #[{ id := { key := "flip" },
               args := #[{ id := "b", typ := GoLean.GoCore.Ty.bool }],
               results := #[{ id := "result", typ := GoLean.GoCore.Ty.bool }],
               body := GoLean.GoCore.Stmt.block
                         #[]
                         #[GoLean.GoCore.Stmt.seqn
                             #[GoLean.GoCore.Stmt.assign
                                 (GoLean.GoCore.Assignee.var "result")
                                 (GoLean.GoCore.Expr.not (GoLean.GoCore.Expr.var "b")),
                               GoLean.GoCore.Stmt.returnStmt]],
               variadic := false,
               wrapper := false },
             { id := { key := "indirectRecover" },
               args := #[],
               results := #[{ id := "result", typ := GoLean.GoCore.Ty.bool }],
               body := GoLean.GoCore.Stmt.block
                         #[]
                         #[GoLean.GoCore.Stmt.seqn
                             #[GoLean.GoCore.Stmt.initialization
                                 { id := "$c0", typ := GoLean.GoCore.Ty.interface { key := "any" } },
                               GoLean.GoCore.Stmt.assign
                                 (GoLean.GoCore.Assignee.var "$c0")
                                 (GoLean.GoCore.Expr.recoverCall)],
                           GoLean.GoCore.Stmt.seqn
                             #[GoLean.GoCore.Stmt.assign
                                 (GoLean.GoCore.Assignee.var "result")
                                 (GoLean.GoCore.Expr.eqCmp
                                   (GoLean.GoCore.Ty.interface { key := "any" })
                                   (GoLean.GoCore.Expr.var "$c0")
                                   (GoLean.GoCore.Expr.nil none)),
                               GoLean.GoCore.Stmt.returnStmt]],
               variadic := false,
               wrapper := false },
             { id := { key := "Shared$lit0" },
               args := #[{ id := "result$cap", typ := GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.bool) }],
               results := #[],
               body := GoLean.GoCore.Stmt.block
                         #[]
                         #[GoLean.GoCore.Stmt.seqn
                             #[GoLean.GoCore.Stmt.call
                                 #[GoLean.GoCore.Assignee.addr (GoLean.GoCore.Expr.var "result$cap")]
                                 { key := "flip" }
                                 #[GoLean.GoCore.Expr.deref
                                     (GoLean.GoCore.Expr.var "result$cap")
                                     (GoLean.GoCore.Ty.bool)]]],
               variadic := false,
               wrapper := false },
             { id := { key := "Shared$lit1" },
               args := #[{ id := "result$cap", typ := GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.bool) }],
               results := #[],
               body := GoLean.GoCore.Stmt.block
                         #[]
                         #[GoLean.GoCore.Stmt.seqn
                             #[GoLean.GoCore.Stmt.initialization { id := "outside", typ := GoLean.GoCore.Ty.bool },
                               GoLean.GoCore.Stmt.call
                                 #[GoLean.GoCore.Assignee.var "outside"]
                                 { key := "indirectRecover" }
                                 #[]],
                           GoLean.GoCore.Stmt.seqn
                             #[GoLean.GoCore.Stmt.initialization
                                 { id := "$c1", typ := GoLean.GoCore.Ty.interface { key := "any" } },
                               GoLean.GoCore.Stmt.assign
                                 (GoLean.GoCore.Assignee.var "$c1")
                                 (GoLean.GoCore.Expr.recoverCall)],
                           GoLean.GoCore.Stmt.ifThenElse
                             (GoLean.GoCore.Expr.neqCmp
                               (GoLean.GoCore.Ty.interface { key := "any" })
                               (GoLean.GoCore.Expr.var "$c1")
                               (GoLean.GoCore.Expr.nil none))
                             (GoLean.GoCore.Stmt.block
                               #[]
                               #[GoLean.GoCore.Stmt.seqn
                                   #[GoLean.GoCore.Stmt.assign
                                       (GoLean.GoCore.Assignee.addr (GoLean.GoCore.Expr.var "result$cap"))
                                       (GoLean.GoCore.Expr.var "outside")]])
                             (GoLean.GoCore.Stmt.seqn #[])],
               variadic := false,
               wrapper := false },
             { id := { key := "Shared" },
               args := #[{ id := "b", typ := GoLean.GoCore.Ty.bool }],
               results := #[{ id := "result", typ := GoLean.GoCore.Ty.bool }],
               body := GoLean.GoCore.Stmt.block
                         #[]
                         #[GoLean.GoCore.Stmt.deferCall
                             (GoLean.GoCore.Expr.funcVal { key := "Shared$lit0" } #[GoLean.GoCore.Expr.ref "result"])
                             #[],
                           GoLean.GoCore.Stmt.deferCall
                             (GoLean.GoCore.Expr.funcVal { key := "Shared$lit1" } #[GoLean.GoCore.Expr.ref "result"])
                             #[],
                           GoLean.GoCore.Stmt.seqn
                             #[GoLean.GoCore.Stmt.call
                                 #[GoLean.GoCore.Assignee.var "result"]
                                 { key := "flip" }
                                 #[GoLean.GoCore.Expr.boolLit true]],
                           GoLean.GoCore.Stmt.ifThenElse
                             (GoLean.GoCore.Expr.var "b")
                             (GoLean.GoCore.Stmt.block
                               #[]
                               #[GoLean.GoCore.Stmt.panicStmt
                                   (GoLean.GoCore.Expr.toInterface
                                     (GoLean.GoCore.Ty.interface { key := "any" })
                                     (GoLean.GoCore.Ty.string)
                                     (GoLean.GoCore.Expr.stringLit
                                       { bytes := #[115, 104, 97, 114, 101, 100, 32, 114, 101, 99, 111, 118, 101, 114,
                                                    121] }))])
                             (GoLean.GoCore.Stmt.seqn #[]),
                           GoLean.GoCore.Stmt.returnStmt],
               variadic := false,
               wrapper := false },
             { id := { key := "Outside" },
               args := #[],
               results := #[{ id := "result", typ := GoLean.GoCore.Ty.bool }],
               body := GoLean.GoCore.Stmt.block
                         #[]
                         #[GoLean.GoCore.Stmt.seqn
                             #[GoLean.GoCore.Stmt.initialization
                                 { id := "$c2", typ := GoLean.GoCore.Ty.interface { key := "any" } },
                               GoLean.GoCore.Stmt.assign
                                 (GoLean.GoCore.Assignee.var "$c2")
                                 (GoLean.GoCore.Expr.recoverCall)],
                           GoLean.GoCore.Stmt.seqn
                             #[GoLean.GoCore.Stmt.assign
                                 (GoLean.GoCore.Assignee.var "result")
                                 (GoLean.GoCore.Expr.eqCmp
                                   (GoLean.GoCore.Ty.interface { key := "any" })
                                   (GoLean.GoCore.Expr.var "$c2")
                                   (GoLean.GoCore.Expr.nil none)),
                               GoLean.GoCore.Stmt.returnStmt]],
               variadic := false,
               wrapper := false },
             { id := { key := "SharedFalse" },
               args := #[],
               results := #[{ id := "result", typ := GoLean.GoCore.Ty.bool }],
               body := GoLean.GoCore.Stmt.block
                         #[]
                         #[GoLean.GoCore.Stmt.seqn
                             #[GoLean.GoCore.Stmt.initialization { id := "$c3", typ := GoLean.GoCore.Ty.bool },
                               GoLean.GoCore.Stmt.call
                                 #[GoLean.GoCore.Assignee.var "$c3"]
                                 { key := "Shared" }
                                 #[GoLean.GoCore.Expr.boolLit false]],
                           GoLean.GoCore.Stmt.seqn
                             #[GoLean.GoCore.Stmt.assign
                                 (GoLean.GoCore.Assignee.var "result")
                                 (GoLean.GoCore.Expr.var "$c3"),
                               GoLean.GoCore.Stmt.returnStmt]],
               variadic := false,
               wrapper := false },
             { id := { key := "SharedTrue" },
               args := #[],
               results := #[{ id := "result", typ := GoLean.GoCore.Ty.bool }],
               body := GoLean.GoCore.Stmt.block
                         #[]
                         #[GoLean.GoCore.Stmt.seqn
                             #[GoLean.GoCore.Stmt.initialization { id := "$c4", typ := GoLean.GoCore.Ty.bool },
                               GoLean.GoCore.Stmt.call
                                 #[GoLean.GoCore.Assignee.var "$c4"]
                                 { key := "Shared" }
                                 #[GoLean.GoCore.Expr.boolLit true]],
                           GoLean.GoCore.Stmt.seqn
                             #[GoLean.GoCore.Stmt.assign
                                 (GoLean.GoCore.Assignee.var "result")
                                 (GoLean.GoCore.Expr.var "$c4"),
                               GoLean.GoCore.Stmt.returnStmt]],
               variadic := false,
               wrapper := false },
             { id := { key := "Reversed$lit0" },
               args := #[{ id := "result$cap", typ := GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.bool) }],
               results := #[],
               body := GoLean.GoCore.Stmt.block
                         #[]
                         #[GoLean.GoCore.Stmt.seqn
                             #[GoLean.GoCore.Stmt.initialization { id := "outside", typ := GoLean.GoCore.Ty.bool },
                               GoLean.GoCore.Stmt.call
                                 #[GoLean.GoCore.Assignee.var "outside"]
                                 { key := "indirectRecover" }
                                 #[]],
                           GoLean.GoCore.Stmt.seqn
                             #[GoLean.GoCore.Stmt.initialization
                                 { id := "$c5", typ := GoLean.GoCore.Ty.interface { key := "any" } },
                               GoLean.GoCore.Stmt.assign
                                 (GoLean.GoCore.Assignee.var "$c5")
                                 (GoLean.GoCore.Expr.recoverCall)],
                           GoLean.GoCore.Stmt.ifThenElse
                             (GoLean.GoCore.Expr.neqCmp
                               (GoLean.GoCore.Ty.interface { key := "any" })
                               (GoLean.GoCore.Expr.var "$c5")
                               (GoLean.GoCore.Expr.nil none))
                             (GoLean.GoCore.Stmt.block
                               #[]
                               #[GoLean.GoCore.Stmt.seqn
                                   #[GoLean.GoCore.Stmt.assign
                                       (GoLean.GoCore.Assignee.addr (GoLean.GoCore.Expr.var "result$cap"))
                                       (GoLean.GoCore.Expr.var "outside")]])
                             (GoLean.GoCore.Stmt.seqn #[])],
               variadic := false,
               wrapper := false },
             { id := { key := "Reversed$lit1" },
               args := #[{ id := "result$cap", typ := GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.bool) }],
               results := #[],
               body := GoLean.GoCore.Stmt.block
                         #[]
                         #[GoLean.GoCore.Stmt.seqn
                             #[GoLean.GoCore.Stmt.call
                                 #[GoLean.GoCore.Assignee.addr (GoLean.GoCore.Expr.var "result$cap")]
                                 { key := "flip" }
                                 #[GoLean.GoCore.Expr.deref
                                     (GoLean.GoCore.Expr.var "result$cap")
                                     (GoLean.GoCore.Ty.bool)]]],
               variadic := false,
               wrapper := false },
             { id := { key := "Reversed" },
               args := #[{ id := "b", typ := GoLean.GoCore.Ty.bool }],
               results := #[{ id := "result", typ := GoLean.GoCore.Ty.bool }],
               body := GoLean.GoCore.Stmt.block
                         #[]
                         #[GoLean.GoCore.Stmt.deferCall
                             (GoLean.GoCore.Expr.funcVal { key := "Reversed$lit0" } #[GoLean.GoCore.Expr.ref "result"])
                             #[],
                           GoLean.GoCore.Stmt.deferCall
                             (GoLean.GoCore.Expr.funcVal { key := "Reversed$lit1" } #[GoLean.GoCore.Expr.ref "result"])
                             #[],
                           GoLean.GoCore.Stmt.seqn
                             #[GoLean.GoCore.Stmt.call
                                 #[GoLean.GoCore.Assignee.var "result"]
                                 { key := "flip" }
                                 #[GoLean.GoCore.Expr.boolLit true]],
                           GoLean.GoCore.Stmt.ifThenElse
                             (GoLean.GoCore.Expr.var "b")
                             (GoLean.GoCore.Stmt.block
                               #[]
                               #[GoLean.GoCore.Stmt.panicStmt
                                   (GoLean.GoCore.Expr.toInterface
                                     (GoLean.GoCore.Ty.interface { key := "any" })
                                     (GoLean.GoCore.Ty.string)
                                     (GoLean.GoCore.Expr.stringLit
                                       { bytes := #[115, 104, 97, 114, 101, 100, 32, 114, 101, 99, 111, 118, 101, 114,
                                                    121] }))])
                             (GoLean.GoCore.Stmt.seqn #[]),
                           GoLean.GoCore.Stmt.returnStmt],
               variadic := false,
               wrapper := false },
             { id := { key := "DirectRecoveryControl$lit0" },
               args := #[{ id := "result$cap", typ := GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.bool) }],
               results := #[],
               body := GoLean.GoCore.Stmt.block
                         #[]
                         #[GoLean.GoCore.Stmt.seqn
                             #[GoLean.GoCore.Stmt.call
                                 #[GoLean.GoCore.Assignee.addr (GoLean.GoCore.Expr.var "result$cap")]
                                 { key := "flip" }
                                 #[GoLean.GoCore.Expr.deref
                                     (GoLean.GoCore.Expr.var "result$cap")
                                     (GoLean.GoCore.Ty.bool)]]],
               variadic := false,
               wrapper := false },
             { id := { key := "DirectRecoveryControl$lit1" },
               args := #[{ id := "result$cap", typ := GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.bool) }],
               results := #[],
               body := GoLean.GoCore.Stmt.block
                         #[]
                         #[GoLean.GoCore.Stmt.seqn
                             #[GoLean.GoCore.Stmt.initialization
                                 { id := "$c6", typ := GoLean.GoCore.Ty.interface { key := "any" } },
                               GoLean.GoCore.Stmt.assign
                                 (GoLean.GoCore.Assignee.var "$c6")
                                 (GoLean.GoCore.Expr.recoverCall)],
                           GoLean.GoCore.Stmt.seqn
                             #[GoLean.GoCore.Stmt.initialization { id := "outside", typ := GoLean.GoCore.Ty.bool },
                               GoLean.GoCore.Stmt.assign
                                 (GoLean.GoCore.Assignee.var "outside")
                                 (GoLean.GoCore.Expr.eqCmp
                                   (GoLean.GoCore.Ty.interface { key := "any" })
                                   (GoLean.GoCore.Expr.var "$c6")
                                   (GoLean.GoCore.Expr.nil none))],
                           GoLean.GoCore.Stmt.seqn
                             #[GoLean.GoCore.Stmt.initialization
                                 { id := "$c7", typ := GoLean.GoCore.Ty.interface { key := "any" } },
                               GoLean.GoCore.Stmt.assign
                                 (GoLean.GoCore.Assignee.var "$c7")
                                 (GoLean.GoCore.Expr.recoverCall)],
                           GoLean.GoCore.Stmt.ifThenElse
                             (GoLean.GoCore.Expr.neqCmp
                               (GoLean.GoCore.Ty.interface { key := "any" })
                               (GoLean.GoCore.Expr.var "$c7")
                               (GoLean.GoCore.Expr.nil none))
                             (GoLean.GoCore.Stmt.block
                               #[]
                               #[GoLean.GoCore.Stmt.seqn
                                   #[GoLean.GoCore.Stmt.assign
                                       (GoLean.GoCore.Assignee.addr (GoLean.GoCore.Expr.var "result$cap"))
                                       (GoLean.GoCore.Expr.var "outside")]])
                             (GoLean.GoCore.Stmt.seqn #[])],
               variadic := false,
               wrapper := false },
             { id := { key := "DirectRecoveryControl" },
               args := #[{ id := "b", typ := GoLean.GoCore.Ty.bool }],
               results := #[{ id := "result", typ := GoLean.GoCore.Ty.bool }],
               body := GoLean.GoCore.Stmt.block
                         #[]
                         #[GoLean.GoCore.Stmt.deferCall
                             (GoLean.GoCore.Expr.funcVal
                               { key := "DirectRecoveryControl$lit0" }
                               #[GoLean.GoCore.Expr.ref "result"])
                             #[],
                           GoLean.GoCore.Stmt.deferCall
                             (GoLean.GoCore.Expr.funcVal
                               { key := "DirectRecoveryControl$lit1" }
                               #[GoLean.GoCore.Expr.ref "result"])
                             #[],
                           GoLean.GoCore.Stmt.seqn
                             #[GoLean.GoCore.Stmt.call
                                 #[GoLean.GoCore.Assignee.var "result"]
                                 { key := "flip" }
                                 #[GoLean.GoCore.Expr.boolLit true]],
                           GoLean.GoCore.Stmt.ifThenElse
                             (GoLean.GoCore.Expr.var "b")
                             (GoLean.GoCore.Stmt.block
                               #[]
                               #[GoLean.GoCore.Stmt.panicStmt
                                   (GoLean.GoCore.Expr.toInterface
                                     (GoLean.GoCore.Ty.interface { key := "any" })
                                     (GoLean.GoCore.Ty.string)
                                     (GoLean.GoCore.Expr.stringLit
                                       { bytes := #[115, 104, 97, 114, 101, 100, 32, 114, 101, 99, 111, 118, 101, 114,
                                                    121] }))])
                             (GoLean.GoCore.Stmt.seqn #[]),
                           GoLean.GoCore.Stmt.returnStmt],
               variadic := false,
               wrapper := false },
             { id := { key := "ReversedTrue" },
               args := #[],
               results := #[{ id := "result", typ := GoLean.GoCore.Ty.bool }],
               body := GoLean.GoCore.Stmt.block
                         #[]
                         #[GoLean.GoCore.Stmt.seqn
                             #[GoLean.GoCore.Stmt.initialization { id := "$c8", typ := GoLean.GoCore.Ty.bool },
                               GoLean.GoCore.Stmt.call
                                 #[GoLean.GoCore.Assignee.var "$c8"]
                                 { key := "Reversed" }
                                 #[GoLean.GoCore.Expr.boolLit true]],
                           GoLean.GoCore.Stmt.seqn
                             #[GoLean.GoCore.Stmt.assign
                                 (GoLean.GoCore.Assignee.var "result")
                                 (GoLean.GoCore.Expr.var "$c8"),
                               GoLean.GoCore.Stmt.returnStmt]],
               variadic := false,
               wrapper := false },
             { id := { key := "DirectTrue" },
               args := #[],
               results := #[{ id := "result", typ := GoLean.GoCore.Ty.bool }],
               body := GoLean.GoCore.Stmt.block
                         #[]
                         #[GoLean.GoCore.Stmt.seqn
                             #[GoLean.GoCore.Stmt.initialization { id := "$c9", typ := GoLean.GoCore.Ty.bool },
                               GoLean.GoCore.Stmt.call
                                 #[GoLean.GoCore.Assignee.var "$c9"]
                                 { key := "DirectRecoveryControl" }
                                 #[GoLean.GoCore.Expr.boolLit true]],
                           GoLean.GoCore.Stmt.seqn
                             #[GoLean.GoCore.Stmt.assign
                                 (GoLean.GoCore.Assignee.var "result")
                                 (GoLean.GoCore.Expr.var "$c9"),
                               GoLean.GoCore.Stmt.returnStmt]],
               variadic := false,
               wrapper := false }],
  methods := #[],
  globals := #[],
  methodSets := #[{ key := "struct{}", coverage := GoLean.GoCore.MethodSetCoverage.full }],
  typeDisplays := #[({ key := "struct{}" }, { name := "struct {}", pkg := "" }),
                    ({ key := "$runtime.Error" },
                     { name := "<runtime error payload: gc's concrete type (runtime.errorString / runtime.boundsError / *runtime.TypeAssertionError / …) is not modeled — one synthetic $runtime.Error id, BUG-009/BUG-053 class>",
                       pkg := "runtime" })] }

set_option maxRecDepth 8192
set_option maxHeartbeats 800000

theorem shared_admitted (b : Bool) :
    checkRecovery nativeRecovery "Shared" #[.bool b] = .ok () := by
  cases b <;> with_unfolding_all rfl

theorem outside_admitted :
    checkRecovery nativeRecovery "Outside" #[] = .ok () := by
  with_unfolding_all rfl

theorem shared_false_admitted :
    checkRecovery nativeRecovery "SharedFalse" #[] = .ok () := by
  with_unfolding_all rfl

theorem shared_true_admitted :
    checkRecovery nativeRecovery "SharedTrue" #[] = .ok () := by
  with_unfolding_all rfl


theorem reversed_control_admitted (b : Bool) :
    checkRecovery nativeRecovery "Reversed" #[.bool b] = .ok () := by
  cases b <;> with_unfolding_all rfl

theorem direct_control_admitted (b : Bool) :
    checkRecovery nativeRecovery "DirectRecoveryControl" #[.bool b] = .ok () := by
  cases b <;> with_unfolding_all rfl

end GoLean.GoCore.RecoveryTyping.Tests
