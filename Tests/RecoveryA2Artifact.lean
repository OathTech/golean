import GoLean.GoCore.RecoveryAdmission
import GoLean.GoCore.Multi

/-! GoCore artifact emitted and lowered from fixtures/recovery/main.go.
The dedicated check compares this value with fresh native lowering. That
comparison is an executable translation check, not a compiler theorem. -/
namespace GoLean.GoCore.RecoveryTyping.Tests
open Machine

def a2Program : Program :=
{ typeDefs := #[({ key := "struct{}" }, GoLean.GoCore.TypeDef.struct #[]),
                ({ key := "$runtime.Error" },
                 GoLean.GoCore.TypeDef.opaqueDecl
                   "the machine's runtime-error payload type ($runtime.Error): structural use (==, normalization or conversion at the type, default value) is unmodeled — gc realizes several runtime.Error types behind one abort text (BUG-059 kind clause), so the machine refuses rather than answers")],
  funcs := #[{ id := { key := "fail" },
               args := #[],
               results := #[],
               body := GoLean.GoCore.Stmt.block
                         #[]
                         #[GoLean.GoCore.Stmt.panicStmt
                             (GoLean.GoCore.Expr.toInterface
                               (GoLean.GoCore.Ty.interface { key := "any" })
                               (GoLean.GoCore.Ty.string)
                               (GoLean.GoCore.Expr.stringLit
                                 { bytes := #[99, 117, 115, 116, 111, 109, 101, 114, 32, 112, 97, 110, 105, 99] }))],
               variadic := false,
               wrapper := false },
             { id := { key := "Recovered$lit0" },
               args := #[{ id := "result$cap", typ := GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.bool) }],
               results := #[],
               body := GoLean.GoCore.Stmt.block
                         #[]
                         #[GoLean.GoCore.Stmt.seqn
                             #[GoLean.GoCore.Stmt.initialization
                                 { id := "$c0", typ := GoLean.GoCore.Ty.interface { key := "any" } },
                               GoLean.GoCore.Stmt.assign
                                 (GoLean.GoCore.Assignee.var "$c0")
                                 (GoLean.GoCore.Expr.recoverCall)],
                           GoLean.GoCore.Stmt.ifThenElse
                             (GoLean.GoCore.Expr.neqCmp
                               (GoLean.GoCore.Ty.interface { key := "any" })
                               (GoLean.GoCore.Expr.var "$c0")
                               (GoLean.GoCore.Expr.nil none))
                             (GoLean.GoCore.Stmt.block
                               #[]
                               #[GoLean.GoCore.Stmt.seqn
                                   #[GoLean.GoCore.Stmt.assign
                                       (GoLean.GoCore.Assignee.addr (GoLean.GoCore.Expr.var "result$cap"))
                                       (GoLean.GoCore.Expr.boolLit true)]])
                             (GoLean.GoCore.Stmt.seqn #[])],
               variadic := false,
               wrapper := false },
             { id := { key := "Recovered" },
               args := #[],
               results := #[{ id := "result", typ := GoLean.GoCore.Ty.bool }],
               body := GoLean.GoCore.Stmt.block
                         #[]
                         #[GoLean.GoCore.Stmt.deferCall
                             (GoLean.GoCore.Expr.funcVal { key := "Recovered$lit0" } #[GoLean.GoCore.Expr.ref "result"])
                             #[],
                           GoLean.GoCore.Stmt.call #[] { key := "fail" } #[],
                           GoLean.GoCore.Stmt.seqn
                             #[GoLean.GoCore.Stmt.assign
                                 (GoLean.GoCore.Assignee.var "result")
                                 (GoLean.GoCore.Expr.boolLit false),
                               GoLean.GoCore.Stmt.returnStmt]],
               variadic := false,
               wrapper := false },
             { id := { key := "Normal" },
               args := #[],
               results := #[{ id := "result", typ := GoLean.GoCore.Ty.bool }],
               body := GoLean.GoCore.Stmt.block
                         #[]
                         #[GoLean.GoCore.Stmt.seqn
                             #[GoLean.GoCore.Stmt.assign
                                 (GoLean.GoCore.Assignee.var "result")
                                 (GoLean.GoCore.Expr.boolLit true)],
                           GoLean.GoCore.Stmt.returnStmt],
               variadic := false,
               wrapper := false },
             { id := { key := "Uncaught" },
               args := #[],
               results := #[],
               body := GoLean.GoCore.Stmt.block #[] #[GoLean.GoCore.Stmt.call #[] { key := "fail" } #[]],
               variadic := false,
               wrapper := false }],
  methods := #[],
  globals := #[],
  methodSets := #[{ key := "struct{}", coverage := GoLean.GoCore.MethodSetCoverage.full }],
  typeDisplays := #[({ key := "struct{}" }, { name := "struct {}", pkg := "" }),
                    ({ key := "$runtime.Error" },
                     { name := "<runtime error payload: gc's concrete type (runtime.errorString / runtime.boundsError / *runtime.TypeAssertionError / …) is not modeled — one synthetic $runtime.Error id, BUG-009/BUG-053 class>",
                       pkg := "runtime" })] }

end GoLean.GoCore.RecoveryTyping.Tests

namespace GoLean.GoCore.RecoveryTyping.Tests
set_option maxRecDepth 4096

theorem a2_recovered : checkRecovery a2Program "Recovered" #[] = .ok () := by
  with_unfolding_all rfl

theorem a2_normal : checkRecovery a2Program "Normal" #[] = .ok () := by
  with_unfolding_all rfl

theorem a2_uncaught : checkRecovery a2Program "Uncaught" #[] = .ok () := by
  with_unfolding_all rfl

end GoLean.GoCore.RecoveryTyping.Tests
