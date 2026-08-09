import GoLean.GoCore.Syntax

/-!
# Pin: decoded(frontend(compat/gobra/testdata/sum/main.go))

The native frontend's ACTUAL lowering of the annotated sum source, checked
in verbatim from `testdata/sum/sum-lowered.repr` (produced by
`testdata/sum/decode.lean`), following the `Specs/GoldenProgram.lean`
golden-pin convention: proof subject = decoded(frontend(source)).
The `//@` Gobra annotations pass through the frontend invisibly —
the wire and this pin are contract-free by construction (spike stage 1;
a `"specs"` wire key is the recorded stage-2 design).
-/

namespace GobraCompat

def sumLowered : GoLean.GoCore.Program :=
{ typeDefs := #[({ key := "struct{}" }, GoLean.GoCore.TypeDef.struct #[])],
  funcs := #[{ id := { key := "sum" },
               args := #[{ id := "n", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int) }],
               results := #[{ id := "sum", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int) }],
               body := GoLean.GoCore.Stmt.block
                         #[]
                         #[GoLean.GoCore.Stmt.seqn
                             #[GoLean.GoCore.Stmt.assign
                                 (GoLean.GoCore.Assignee.var "sum")
                                 (GoLean.GoCore.Expr.intLit 0 (GoLean.GoCore.IntKind.int))],
                           GoLean.GoCore.Stmt.block
                             #[]
                             #[GoLean.GoCore.Stmt.seqn
                                 #[GoLean.GoCore.Stmt.initialization
                                     { id := "i", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int) },
                                   GoLean.GoCore.Stmt.assign
                                     (GoLean.GoCore.Assignee.var "i")
                                     (GoLean.GoCore.Expr.intLit 0 (GoLean.GoCore.IntKind.int))],
                               GoLean.GoCore.Stmt.block
                                 #[]
                                 #[GoLean.GoCore.Stmt.initialization
                                     { id := "$forFirst", typ := GoLean.GoCore.Ty.bool },
                                   GoLean.GoCore.Stmt.assign
                                     (GoLean.GoCore.Assignee.var "$forFirst")
                                     (GoLean.GoCore.Expr.boolLit true),
                                   GoLean.GoCore.Stmt.while
                                     (GoLean.GoCore.Expr.boolLit true)
                                     (GoLean.GoCore.Stmt.block
                                       #[]
                                       #[GoLean.GoCore.Stmt.ifThenElse
                                           (GoLean.GoCore.Expr.var "$forFirst")
                                           (GoLean.GoCore.Stmt.assign
                                             (GoLean.GoCore.Assignee.var "$forFirst")
                                             (GoLean.GoCore.Expr.boolLit false))
                                           (GoLean.GoCore.Stmt.assign
                                             (GoLean.GoCore.Assignee.var "i")
                                             (GoLean.GoCore.Expr.add
                                               (GoLean.GoCore.Expr.var "i")
                                               (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.int)))),
                                         GoLean.GoCore.Stmt.seqn #[],
                                         GoLean.GoCore.Stmt.ifThenElse
                                           (GoLean.GoCore.Expr.atMostCmp
                                             (GoLean.GoCore.Expr.var "i")
                                             (GoLean.GoCore.Expr.var "n"))
                                           (GoLean.GoCore.Stmt.seqn #[])
                                           (GoLean.GoCore.Stmt.breakStmt),
                                         GoLean.GoCore.Stmt.block
                                           #[]
                                           #[GoLean.GoCore.Stmt.assign
                                               (GoLean.GoCore.Assignee.var "sum")
                                               (GoLean.GoCore.Expr.add
                                                 (GoLean.GoCore.Expr.var "sum")
                                                 (GoLean.GoCore.Expr.var "i"))]])]],
                           GoLean.GoCore.Stmt.seqn
                             #[GoLean.GoCore.Stmt.assign
                                 (GoLean.GoCore.Assignee.var "sum")
                                 (GoLean.GoCore.Expr.var "sum"),
                               GoLean.GoCore.Stmt.returnStmt]],
               variadic := false,
               wrapper := false },
             { id := { key := "sumZero" },
               args := #[],
               results := #[{ id := "$res0", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int) }],
               body := GoLean.GoCore.Stmt.block
                         #[]
                         #[GoLean.GoCore.Stmt.seqn
                             #[GoLean.GoCore.Stmt.initialization
                                 { id := "$c0", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int) },
                               GoLean.GoCore.Stmt.call
                                 #[GoLean.GoCore.Assignee.var "$c0"]
                                 { key := "sum" }
                                 #[GoLean.GoCore.Expr.intLit 0 (GoLean.GoCore.IntKind.int)]],
                           GoLean.GoCore.Stmt.seqn
                             #[GoLean.GoCore.Stmt.assign
                                 (GoLean.GoCore.Assignee.var "$res0")
                                 (GoLean.GoCore.Expr.var "$c0"),
                               GoLean.GoCore.Stmt.returnStmt]],
               variadic := false,
               wrapper := false },
             { id := { key := "sumOne" },
               args := #[],
               results := #[{ id := "$res0", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int) }],
               body := GoLean.GoCore.Stmt.block
                         #[]
                         #[GoLean.GoCore.Stmt.seqn
                             #[GoLean.GoCore.Stmt.initialization
                                 { id := "$c1", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int) },
                               GoLean.GoCore.Stmt.call
                                 #[GoLean.GoCore.Assignee.var "$c1"]
                                 { key := "sum" }
                                 #[GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.int)]],
                           GoLean.GoCore.Stmt.seqn
                             #[GoLean.GoCore.Stmt.assign
                                 (GoLean.GoCore.Assignee.var "$res0")
                                 (GoLean.GoCore.Expr.var "$c1"),
                               GoLean.GoCore.Stmt.returnStmt]],
               variadic := false,
               wrapper := false },
             { id := { key := "sumFive" },
               args := #[],
               results := #[{ id := "$res0", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int) }],
               body := GoLean.GoCore.Stmt.block
                         #[]
                         #[GoLean.GoCore.Stmt.seqn
                             #[GoLean.GoCore.Stmt.initialization
                                 { id := "$c2", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int) },
                               GoLean.GoCore.Stmt.call
                                 #[GoLean.GoCore.Assignee.var "$c2"]
                                 { key := "sum" }
                                 #[GoLean.GoCore.Expr.intLit 5 (GoLean.GoCore.IntKind.int)]],
                           GoLean.GoCore.Stmt.seqn
                             #[GoLean.GoCore.Stmt.assign
                                 (GoLean.GoCore.Assignee.var "$res0")
                                 (GoLean.GoCore.Expr.var "$c2"),
                               GoLean.GoCore.Stmt.returnStmt]],
               variadic := false,
               wrapper := false },
             { id := { key := "sumTwelve" },
               args := #[],
               results := #[{ id := "$res0", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int) }],
               body := GoLean.GoCore.Stmt.block
                         #[]
                         #[GoLean.GoCore.Stmt.seqn
                             #[GoLean.GoCore.Stmt.initialization
                                 { id := "$c3", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int) },
                               GoLean.GoCore.Stmt.call
                                 #[GoLean.GoCore.Assignee.var "$c3"]
                                 { key := "sum" }
                                 #[GoLean.GoCore.Expr.intLit 12 (GoLean.GoCore.IntKind.int)]],
                           GoLean.GoCore.Stmt.seqn
                             #[GoLean.GoCore.Stmt.assign
                                 (GoLean.GoCore.Assignee.var "$res0")
                                 (GoLean.GoCore.Expr.var "$c3"),
                               GoLean.GoCore.Stmt.returnStmt]],
               variadic := false,
               wrapper := false }],
  methods := #[],
  globals := #[] }

end GobraCompat
