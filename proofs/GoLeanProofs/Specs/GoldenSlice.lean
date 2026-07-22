import GoLean.GoCore.Correspondence
import GoLeanProofs.Specs.SliceCorrespondence

/-!
# The golden-lowered slice (arc `exit-infra`)

`sliceLowered` is the native frontend's ACTUAL lowering of the slice source
(`Corpus/coverage/exec/pointers/inc-via-call/main.go`) — the very term the
differential harness executes against `go run`. It is checked in as a Lean
literal (generated from the decoder's `repr`; `scripts/check-golden`
verifies BOTH links: fresh frontend+decode reproduces
`baselines/golden/slice-lowered.repr`, and this term prints the same repr —
so "proof subject = decoded(frontend(source))" is machine-checked, fail
closed, on every CI run).

The lowered shape exercises everything Arc C built: nested `.seqn`
declaration groups (D1 splice), the `$res0` synthesized result with its
`.seqn`-grouped return, and `.block`-wrapped bodies (whose internal inits
pop before frame exit — D2-proper makes the result read immune to them, so
NO avoid-condition is needed anywhere in this file).

The driver statement (`goldenProg`: `r := 0; r = incViaCall()`) is ours —
the minimal harness action "call the subject function into a cell",
mirroring what the differential runner does via `runNamedFunction`.
-/

namespace GoLean.Iris.GoldenSlice

open GoLean GoLean.GoCore GoLean.GoCore.Rel GoLean.GoCore.Correspondence

/-- The frontend's lowering of the slice source, verbatim
(`scripts/check-golden` pins it). -/
def sliceLowered : Program :=
  { typeDefs := #[({ key := "struct{}" }, GoLean.GoCore.TypeDef.struct #[])],
    funcs := #[{ id := { key := "inc" },
                 args := #[{ id := "p",
                             typ := GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int)) }],
                 results := #[],
                 body := GoLean.GoCore.Stmt.block
                           #[]
                           #[GoLean.GoCore.Stmt.seqn
                               #[GoLean.GoCore.Stmt.assign
                                   (GoLean.GoCore.Assignee.addr (GoLean.GoCore.Expr.var "p"))
                                   (GoLean.GoCore.Expr.add
                                     (GoLean.GoCore.Expr.deref
                                       (GoLean.GoCore.Expr.var "p")
                                       (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int)))
                                     (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.int)))]] },
               { id := { key := "incViaCall" },
                 args := #[],
                 results := #[{ id := "$res0", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int) }],
                 body := GoLean.GoCore.Stmt.block
                           #[]
                           #[GoLean.GoCore.Stmt.seqn
                               #[GoLean.GoCore.Stmt.initialization
                                   { id := "x", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int) },
                                 GoLean.GoCore.Stmt.assign
                                   (GoLean.GoCore.Assignee.var "x")
                                   (GoLean.GoCore.Expr.intLit 0 (GoLean.GoCore.IntKind.int))],
                             GoLean.GoCore.Stmt.call #[] { key := "inc" } #[GoLean.GoCore.Expr.ref "x"],
                             GoLean.GoCore.Stmt.call #[] { key := "inc" } #[GoLean.GoCore.Expr.ref "x"],
                             GoLean.GoCore.Stmt.seqn
                               #[GoLean.GoCore.Stmt.assign
                                   (GoLean.GoCore.Assignee.var "$res0")
                                   (GoLean.GoCore.Expr.var "x"),
                                 GoLean.GoCore.Stmt.returnStmt]] }],
    methods := #[] }

/-- The initial state carrying the golden program's functions. -/
def σg : ExecState := { functions := sliceLowered.funcs }

/-- The driver: allocate the result cell, call the subject into it. -/
abbrev goldenProg : Stmt :=
  .seqn #[.initialization ⟨"r", .int .int⟩,
          .call #[.var "r"] ⟨"incViaCall"⟩ #[]]

/-- The golden initial state satisfies the program invariant: both lowered
functions are fragment functions — `.block`-wrapped bodies (bare NS for
`inc`; a spine with the D1 nested declaration/return groups for
`incViaCall`). -/
theorem σg_inv : StInv σg where
  heap := by intro loc cell h; simp [σg, Heap.lookup] at h
  methods := rfl
  funcs := by
    intro f hf
    simp [σg, sliceLowered] at hf
    rcases hf with rfl | rfl
    · -- inc
      refine ⟨?_, ?_, ?_⟩
      · intro p hp
        simp at hp
        subst hp
        exact .pointer _
      · intro r hr
        simp at hr
      · right
        refine .block (by intro p hp; simp at hp) ?_
        intro s hs
        simp at hs
        subst hs
        exact .seqnSpine (by
          intro q hq
          simp at hq
          subst hq
          exact .ns (.assign (.addr (.var _))
            (.add (.deref _ (.var _)) (.intLit 1 .int))))
    · -- incViaCall
      refine ⟨?_, ?_, ?_⟩
      · intro p hp
        simp at hp
      · intro r hr
        simp at hr
        subst hr
        exact .int _
      · right
        refine .block (by intro p hp; simp at hp) ?_
        intro s hs
        simp at hs
        rcases hs with rfl | rfl | rfl
        · exact .seqnSpine (by
            intro q hq
            simp at hq
            rcases hq with rfl | rfl
            · exact .init (.int _) (by simp)
            · exact .ns (.assign (.var _) (.intLit 0 .int)))
        · exact .ns (.call (by intro a ha; simp at ha)
            (by intro e he; simp at he; subst he; exact .ref _))
        · exact .seqnSpine (by
            intro q hq
            simp at hq
            rcases hq with rfl | rfl
            · exact .ns (.assign (.var _) (.var _))
            · exact .ns .returnStmt)

/-- **The golden correspondence witness.** Every normal interpreter run of
the driver over THE FRONTEND'S ACTUAL LOWERING is a relation execution —
the manual "hand model ≈ lowering" claim is retired for the correspondence
side: the proof subject IS the executed artifact (pinned by
`scripts/check-golden`). -/
theorem golden_interp_run_in_relation (fuel : Nat) (σf : ExecState)
    (ch' : Choices)
    (hrun : execStmt fuel σg [] goldenProg = .ok (.normal σf, ch')) :
    Steps (.exec goldenProg [] .stop) σg (.next .stop)
      (σf.withLocals []) := by
  refine interpreterSound_spineSeq fuel σg σf _ [] ch' ?_ σg_inv hrun
  intro s hs
  simp at hs
  rcases hs with rfl | rfl
  · exact .init (.int _) (by simp)
  · exact .ns (.call
      (by intro a ha; simp at ha; subst ha; exact .var _)
      (by intro e he; simp at he))

end GoLean.Iris.GoldenSlice
