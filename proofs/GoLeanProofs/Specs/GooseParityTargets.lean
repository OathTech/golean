import GoLean.GoCore.MultiStreams
import GoLeanProofs.Surface
import GoLeanProofs.Specs.ImportedGooseActris

/-!
# The spec-parity statement targets — DEFS ONLY (statement module)

The definitions the DESIGNATED spec-parity statements reference
(D3 curation, user ruling 2026-08-10: `compareNilToNilSpecC` +
`compareNilToNilReadoutC` and the fuel-free `dspCert` +
`dspAllSchedules` join the designated set): the imported-goose
TotalPins seed convention (`importedSeed`/`importedEnv`/
`importedCell0`/`importedCellV`, from `Specs/GooseParityKit.lean`),
the pinned nil lowering (`nilLowered`, from
`Specs/ImportedGooseNil.lean` — which keeps its R2 pin THEOREMS and
therefore may not join the trusted closure) and its driver
(`compareNilDriver`, from `Specs/GooseParityNilWP.lean`), and the
channel-certificate seed kit + the dsp row's subjects (`chanSeed`/
`intCell0`/`cellIsInt`, `dspDriver`/`dspEnv`/`dspSeed`, from
`Specs/GooseParityChannels.lean`; `actrisLowered` rides in from its
own module, which is ALREADY def-only).

The F4 def-only-hoist discipline (`ForkJoinTargets` precedent): the
Comparator Challenge — the judge's trusted root — imports ONLY clean
statement modules (defs a skeptic reads, zero theorems); the proofs
stay in their theorem modules, which import THIS file and reach the
judge only through `Solution`. Every def here is MOVED text, never
restated; namespaces (and hence the `check-imported-pins` registry
fqn for `nilLowered`) are unchanged. The ci surface-purity scan pins
this file's imports; the statement-TCB closure gate asserts no
designated theorem is declared in Challenge's closure.
-/

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Surface

namespace GoLean.ImportedGoose

set_option maxRecDepth 1000000

/-! ## The imported-goose TotalPins seed convention (ex-kit) -/

/-- The TotalPins seed for an imported program: the harness-owned output
cell at base address 0, `nextAddr = 1` (the convention every imported
R2 pin already uses). -/
def importedSeed (p : Program) : ExecState :=
  { types := p.typeDefs.toList,
    functions := p.funcs,
    methods := p.methods,
    heap := [(.base ⟨0⟩, ⟨some (.int .int), .int 0 .int⟩)],
    nextAddr := 1 }

/-- Driver env: `r` names the harness output cell (the convention). -/
abbrev importedEnv : LocalEnv := [[("r", .base ⟨0⟩)]]

/-- The seeded-cell precondition `r ↦ 0`. -/
def importedCell0 : HProp := .pointsTo 0 ⟨some (.int .int), .int 0 .int⟩

/-- The verdict postcondition `r ↦ v`. -/
def importedCellV (v : Int) : HProp :=
  .pointsTo 0 ⟨some (.int .int), .int v .int⟩

/-! ## The channel-certificate seed kit (ex-GooseParityChannels; the
muxer-only `strCell0`/`cellIsStr` stayed behind) -/

/-- The TotalPins-style seed with a caller-typed harness cell at base
address 0 (the string-returning muxer wrappers need a string cell; the
int convention is `importedSeed`'s). -/
def chanSeed (p : Program) (cell : HeapCell) : ExecState :=
  { types := p.typeDefs.toList,
    functions := p.funcs,
    methods := p.methods,
    heap := [(.base ⟨0⟩, cell)],
    nextAddr := 1 }

/-- Int harness cell / seed / readout (the imported convention). -/
abbrev intCell0 : HeapCell := ⟨some (.int .int), .int 0 .int⟩

/-- The verdict readout: the harness cell holds exactly `int v`. -/
def cellIsInt (v : Int) : ExecState → Bool := fun σf =>
  match loadLoc σf (.base ⟨0⟩) with
  | .ok (.int w .int) => w == v
  | _ => false


namespace SemanticsNil

/-! ## The pinned nil lowering (ex-ImportedGooseNil) and the exemplar
driver (ex-GooseParityNilWP) -/

/-- The frontend's lowering of the imported case, verbatim (generated
at import; see module docstring for the staleness caveat). -/
def nilLowered : Program :=
  { typeDefs := #[({ key := "struct{}" }, GoLean.GoCore.TypeDef.struct #[])],
    funcs := #[{ id := { key := "testCompareSliceToNil" },
                 args := #[],
                 results := #[{ id := "$res0", typ := GoLean.GoCore.Ty.bool }],
                 body := GoLean.GoCore.Stmt.block
                           #[]
                           #[GoLean.GoCore.Stmt.seqn
                               #[GoLean.GoCore.Stmt.initialization
                                   { id := "$c0",
                                     typ := GoLean.GoCore.Ty.slice (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint8)) },
                                 GoLean.GoCore.Stmt.makeSlice
                                   (GoLean.GoCore.Assignee.var "$c0")
                                   (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint8))
                                   (GoLean.GoCore.Expr.intLit 0 (GoLean.GoCore.IntKind.int))
                                   none],
                             GoLean.GoCore.Stmt.seqn
                               #[GoLean.GoCore.Stmt.initialization
                                   { id := "s",
                                     typ := GoLean.GoCore.Ty.slice (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint8)) },
                                 GoLean.GoCore.Stmt.assign
                                   (GoLean.GoCore.Assignee.var "s")
                                   (GoLean.GoCore.Expr.var "$c0")],
                             GoLean.GoCore.Stmt.seqn
                               #[GoLean.GoCore.Stmt.assign
                                   (GoLean.GoCore.Assignee.var "$res0")
                                   (GoLean.GoCore.Expr.neqCmp
                                     (GoLean.GoCore.Ty.slice (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint8)))
                                     (GoLean.GoCore.Expr.var "s")
                                     (GoLean.GoCore.Expr.nil none)),
                                 GoLean.GoCore.Stmt.returnStmt]],
                 variadic := false,
                 wrapper := false },
               { id := { key := "testComparePointerToNil" },
                 args := #[],
                 results := #[{ id := "$res0", typ := GoLean.GoCore.Ty.bool }],
                 body := GoLean.GoCore.Stmt.block
                           #[]
                           #[GoLean.GoCore.Stmt.seqn
                               #[GoLean.GoCore.Stmt.initialization
                                   { id := "$c1",
                                     typ := GoLean.GoCore.Ty.pointer
                                              (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)) },
                                 GoLean.GoCore.Stmt.newValue
                                   (GoLean.GoCore.Assignee.var "$c1")
                                   (GoLean.GoCore.Expr.defaultValue (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)))
                                   (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)))],
                             GoLean.GoCore.Stmt.seqn
                               #[GoLean.GoCore.Stmt.initialization
                                   { id := "s",
                                     typ := GoLean.GoCore.Ty.pointer
                                              (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)) },
                                 GoLean.GoCore.Stmt.assign
                                   (GoLean.GoCore.Assignee.var "s")
                                   (GoLean.GoCore.Expr.var "$c1")],
                             GoLean.GoCore.Stmt.seqn
                               #[GoLean.GoCore.Stmt.assign
                                   (GoLean.GoCore.Assignee.var "$res0")
                                   (GoLean.GoCore.Expr.neqCmp
                                     (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)))
                                     (GoLean.GoCore.Expr.var "s")
                                     (GoLean.GoCore.Expr.nil none)),
                                 GoLean.GoCore.Stmt.returnStmt]],
                 variadic := false,
                 wrapper := false },
               { id := { key := "testCompareNilToNil" },
                 args := #[],
                 results := #[{ id := "$res0", typ := GoLean.GoCore.Ty.bool }],
                 body := GoLean.GoCore.Stmt.block
                           #[]
                           #[GoLean.GoCore.Stmt.seqn
                               #[GoLean.GoCore.Stmt.initialization
                                   { id := "$c2",
                                     typ := GoLean.GoCore.Ty.pointer
                                              (GoLean.GoCore.Ty.pointer
                                                (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) },
                                 GoLean.GoCore.Stmt.newValue
                                   (GoLean.GoCore.Assignee.var "$c2")
                                   (GoLean.GoCore.Expr.defaultValue
                                     (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))))
                                   (some (GoLean.GoCore.Ty.pointer
                                      (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))))],
                             GoLean.GoCore.Stmt.seqn
                               #[GoLean.GoCore.Stmt.initialization
                                   { id := "s",
                                     typ := GoLean.GoCore.Ty.pointer
                                              (GoLean.GoCore.Ty.pointer
                                                (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) },
                                 GoLean.GoCore.Stmt.assign
                                   (GoLean.GoCore.Assignee.var "s")
                                   (GoLean.GoCore.Expr.var "$c2")],
                             GoLean.GoCore.Stmt.seqn
                               #[GoLean.GoCore.Stmt.assign
                                   (GoLean.GoCore.Assignee.var "$res0")
                                   (GoLean.GoCore.Expr.eqCmp
                                     (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)))
                                     (GoLean.GoCore.Expr.deref
                                       (GoLean.GoCore.Expr.var "s")
                                       (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))))
                                     (GoLean.GoCore.Expr.nil none)),
                                 GoLean.GoCore.Stmt.returnStmt]],
                 variadic := false,
                 wrapper := false },
               { id := { key := "testComparePointerWrappedToNil" },
                 args := #[],
                 results := #[{ id := "$res0", typ := GoLean.GoCore.Ty.bool }],
                 body := GoLean.GoCore.Stmt.block
                           #[]
                           #[GoLean.GoCore.Stmt.seqn
                               #[GoLean.GoCore.Stmt.initialization
                                   { id := "s",
                                     typ := GoLean.GoCore.Ty.slice
                                              (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint8)) }],
                             GoLean.GoCore.Stmt.seqn
                               #[GoLean.GoCore.Stmt.initialization
                                   { id := "$c3",
                                     typ := GoLean.GoCore.Ty.slice (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint8)) },
                                 GoLean.GoCore.Stmt.makeSlice
                                   (GoLean.GoCore.Assignee.var "$c3")
                                   (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint8))
                                   (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.int))
                                   none],
                             GoLean.GoCore.Stmt.seqn
                               #[GoLean.GoCore.Stmt.assign
                                   (GoLean.GoCore.Assignee.var "s")
                                   (GoLean.GoCore.Expr.var "$c3")],
                             GoLean.GoCore.Stmt.seqn
                               #[GoLean.GoCore.Stmt.assign
                                   (GoLean.GoCore.Assignee.var "$res0")
                                   (GoLean.GoCore.Expr.neqCmp
                                     (GoLean.GoCore.Ty.slice (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint8)))
                                     (GoLean.GoCore.Expr.var "s")
                                     (GoLean.GoCore.Expr.nil none)),
                                 GoLean.GoCore.Stmt.returnStmt]],
                 variadic := false,
                 wrapper := false },
               { id := { key := "testComparePointerWrappedDefaultToNil" },
                 args := #[],
                 results := #[{ id := "$res0", typ := GoLean.GoCore.Ty.bool }],
                 body := GoLean.GoCore.Stmt.block
                           #[]
                           #[GoLean.GoCore.Stmt.seqn
                               #[GoLean.GoCore.Stmt.initialization
                                   { id := "s",
                                     typ := GoLean.GoCore.Ty.slice
                                              (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint8)) }],
                             GoLean.GoCore.Stmt.seqn
                               #[GoLean.GoCore.Stmt.assign
                                   (GoLean.GoCore.Assignee.var "$res0")
                                   (GoLean.GoCore.Expr.eqCmp
                                     (GoLean.GoCore.Ty.slice (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint8)))
                                     (GoLean.GoCore.Expr.var "s")
                                     (GoLean.GoCore.Expr.nil none)),
                                 GoLean.GoCore.Stmt.returnStmt]],
                 variadic := false,
                 wrapper := false },
               { id := { key := "testInterfaceNilWithType" },
                 args := #[],
                 results := #[{ id := "$res0", typ := GoLean.GoCore.Ty.bool }],
                 body := GoLean.GoCore.Stmt.block
                           #[]
                           #[GoLean.GoCore.Stmt.seqn
                               #[GoLean.GoCore.Stmt.initialization
                                   { id := "isNil", typ := GoLean.GoCore.Ty.interface { key := "any" } },
                                 GoLean.GoCore.Stmt.assign
                                   (GoLean.GoCore.Assignee.var "isNil")
                                   (GoLean.GoCore.Expr.nil none)],
                             GoLean.GoCore.Stmt.seqn
                               #[GoLean.GoCore.Stmt.initialization
                                   { id := "notNil", typ := GoLean.GoCore.Ty.interface { key := "any" } },
                                 GoLean.GoCore.Stmt.assign
                                   (GoLean.GoCore.Assignee.var "notNil")
                                   (GoLean.GoCore.Expr.toInterface
                                     (GoLean.GoCore.Ty.interface { key := "any" })
                                     (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.string))
                                     (GoLean.GoCore.Expr.convert
                                       (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.string))
                                       (GoLean.GoCore.Expr.nil none)))],
                             GoLean.GoCore.Stmt.seqn
                               #[GoLean.GoCore.Stmt.assign
                                   (GoLean.GoCore.Assignee.var "$res0")
                                   (GoLean.GoCore.Expr.and
                                     (GoLean.GoCore.Expr.and
                                       (GoLean.GoCore.Expr.eqCmp
                                         (GoLean.GoCore.Ty.interface { key := "any" })
                                         (GoLean.GoCore.Expr.var "isNil")
                                         (GoLean.GoCore.Expr.nil none))
                                       (GoLean.GoCore.Expr.neqCmp
                                         (GoLean.GoCore.Ty.interface { key := "any" })
                                         (GoLean.GoCore.Expr.var "notNil")
                                         (GoLean.GoCore.Expr.nil none)))
                                     (GoLean.GoCore.Expr.neqCmp
                                       (GoLean.GoCore.Ty.interface { key := "any" })
                                       (GoLean.GoCore.Expr.var "isNil")
                                       (GoLean.GoCore.Expr.var "notNil"))),
                                 GoLean.GoCore.Stmt.returnStmt]],
                 variadic := false,
                 wrapper := false },
               { id := { key := "goleanTestCompareSliceToNil" },
                 args := #[],
                 results := #[{ id := "$res0", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int) }],
                 body := GoLean.GoCore.Stmt.block
                           #[]
                           #[GoLean.GoCore.Stmt.seqn
                               #[GoLean.GoCore.Stmt.initialization { id := "$c4", typ := GoLean.GoCore.Ty.bool },
                                 GoLean.GoCore.Stmt.call
                                   #[GoLean.GoCore.Assignee.var "$c4"]
                                   { key := "testCompareSliceToNil" }
                                   #[]],
                             GoLean.GoCore.Stmt.ifThenElse
                               (GoLean.GoCore.Expr.var "$c4")
                               (GoLean.GoCore.Stmt.block
                                 #[]
                                 #[GoLean.GoCore.Stmt.seqn
                                     #[GoLean.GoCore.Stmt.assign
                                         (GoLean.GoCore.Assignee.var "$res0")
                                         (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.int)),
                                       GoLean.GoCore.Stmt.returnStmt]])
                               (GoLean.GoCore.Stmt.seqn #[]),
                             GoLean.GoCore.Stmt.seqn
                               #[GoLean.GoCore.Stmt.assign
                                   (GoLean.GoCore.Assignee.var "$res0")
                                   (GoLean.GoCore.Expr.intLit 0 (GoLean.GoCore.IntKind.int)),
                                 GoLean.GoCore.Stmt.returnStmt]],
                 variadic := false,
                 wrapper := false },
               { id := { key := "goleanTestComparePointerToNil" },
                 args := #[],
                 results := #[{ id := "$res0", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int) }],
                 body := GoLean.GoCore.Stmt.block
                           #[]
                           #[GoLean.GoCore.Stmt.seqn
                               #[GoLean.GoCore.Stmt.initialization { id := "$c5", typ := GoLean.GoCore.Ty.bool },
                                 GoLean.GoCore.Stmt.call
                                   #[GoLean.GoCore.Assignee.var "$c5"]
                                   { key := "testComparePointerToNil" }
                                   #[]],
                             GoLean.GoCore.Stmt.ifThenElse
                               (GoLean.GoCore.Expr.var "$c5")
                               (GoLean.GoCore.Stmt.block
                                 #[]
                                 #[GoLean.GoCore.Stmt.seqn
                                     #[GoLean.GoCore.Stmt.assign
                                         (GoLean.GoCore.Assignee.var "$res0")
                                         (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.int)),
                                       GoLean.GoCore.Stmt.returnStmt]])
                               (GoLean.GoCore.Stmt.seqn #[]),
                             GoLean.GoCore.Stmt.seqn
                               #[GoLean.GoCore.Stmt.assign
                                   (GoLean.GoCore.Assignee.var "$res0")
                                   (GoLean.GoCore.Expr.intLit 0 (GoLean.GoCore.IntKind.int)),
                                 GoLean.GoCore.Stmt.returnStmt]],
                 variadic := false,
                 wrapper := false },
               { id := { key := "goleanTestCompareNilToNil" },
                 args := #[],
                 results := #[{ id := "$res0", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int) }],
                 body := GoLean.GoCore.Stmt.block
                           #[]
                           #[GoLean.GoCore.Stmt.seqn
                               #[GoLean.GoCore.Stmt.initialization { id := "$c6", typ := GoLean.GoCore.Ty.bool },
                                 GoLean.GoCore.Stmt.call
                                   #[GoLean.GoCore.Assignee.var "$c6"]
                                   { key := "testCompareNilToNil" }
                                   #[]],
                             GoLean.GoCore.Stmt.ifThenElse
                               (GoLean.GoCore.Expr.var "$c6")
                               (GoLean.GoCore.Stmt.block
                                 #[]
                                 #[GoLean.GoCore.Stmt.seqn
                                     #[GoLean.GoCore.Stmt.assign
                                         (GoLean.GoCore.Assignee.var "$res0")
                                         (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.int)),
                                       GoLean.GoCore.Stmt.returnStmt]])
                               (GoLean.GoCore.Stmt.seqn #[]),
                             GoLean.GoCore.Stmt.seqn
                               #[GoLean.GoCore.Stmt.assign
                                   (GoLean.GoCore.Assignee.var "$res0")
                                   (GoLean.GoCore.Expr.intLit 0 (GoLean.GoCore.IntKind.int)),
                                 GoLean.GoCore.Stmt.returnStmt]],
                 variadic := false,
                 wrapper := false },
               { id := { key := "goleanTestComparePointerWrappedToNil" },
                 args := #[],
                 results := #[{ id := "$res0", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int) }],
                 body := GoLean.GoCore.Stmt.block
                           #[]
                           #[GoLean.GoCore.Stmt.seqn
                               #[GoLean.GoCore.Stmt.initialization { id := "$c7", typ := GoLean.GoCore.Ty.bool },
                                 GoLean.GoCore.Stmt.call
                                   #[GoLean.GoCore.Assignee.var "$c7"]
                                   { key := "testComparePointerWrappedToNil" }
                                   #[]],
                             GoLean.GoCore.Stmt.ifThenElse
                               (GoLean.GoCore.Expr.var "$c7")
                               (GoLean.GoCore.Stmt.block
                                 #[]
                                 #[GoLean.GoCore.Stmt.seqn
                                     #[GoLean.GoCore.Stmt.assign
                                         (GoLean.GoCore.Assignee.var "$res0")
                                         (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.int)),
                                       GoLean.GoCore.Stmt.returnStmt]])
                               (GoLean.GoCore.Stmt.seqn #[]),
                             GoLean.GoCore.Stmt.seqn
                               #[GoLean.GoCore.Stmt.assign
                                   (GoLean.GoCore.Assignee.var "$res0")
                                   (GoLean.GoCore.Expr.intLit 0 (GoLean.GoCore.IntKind.int)),
                                 GoLean.GoCore.Stmt.returnStmt]],
                 variadic := false,
                 wrapper := false },
               { id := { key := "goleanTestComparePointerWrappedDefaultToNil" },
                 args := #[],
                 results := #[{ id := "$res0", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int) }],
                 body := GoLean.GoCore.Stmt.block
                           #[]
                           #[GoLean.GoCore.Stmt.seqn
                               #[GoLean.GoCore.Stmt.initialization { id := "$c8", typ := GoLean.GoCore.Ty.bool },
                                 GoLean.GoCore.Stmt.call
                                   #[GoLean.GoCore.Assignee.var "$c8"]
                                   { key := "testComparePointerWrappedDefaultToNil" }
                                   #[]],
                             GoLean.GoCore.Stmt.ifThenElse
                               (GoLean.GoCore.Expr.var "$c8")
                               (GoLean.GoCore.Stmt.block
                                 #[]
                                 #[GoLean.GoCore.Stmt.seqn
                                     #[GoLean.GoCore.Stmt.assign
                                         (GoLean.GoCore.Assignee.var "$res0")
                                         (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.int)),
                                       GoLean.GoCore.Stmt.returnStmt]])
                               (GoLean.GoCore.Stmt.seqn #[]),
                             GoLean.GoCore.Stmt.seqn
                               #[GoLean.GoCore.Stmt.assign
                                   (GoLean.GoCore.Assignee.var "$res0")
                                   (GoLean.GoCore.Expr.intLit 0 (GoLean.GoCore.IntKind.int)),
                                 GoLean.GoCore.Stmt.returnStmt]],
                 variadic := false,
                 wrapper := false },
               { id := { key := "goleanTestInterfaceNilWithType" },
                 args := #[],
                 results := #[{ id := "$res0", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int) }],
                 body := GoLean.GoCore.Stmt.block
                           #[]
                           #[GoLean.GoCore.Stmt.seqn
                               #[GoLean.GoCore.Stmt.initialization { id := "$c9", typ := GoLean.GoCore.Ty.bool },
                                 GoLean.GoCore.Stmt.call
                                   #[GoLean.GoCore.Assignee.var "$c9"]
                                   { key := "testInterfaceNilWithType" }
                                   #[]],
                             GoLean.GoCore.Stmt.ifThenElse
                               (GoLean.GoCore.Expr.var "$c9")
                               (GoLean.GoCore.Stmt.block
                                 #[]
                                 #[GoLean.GoCore.Stmt.seqn
                                     #[GoLean.GoCore.Stmt.assign
                                         (GoLean.GoCore.Assignee.var "$res0")
                                         (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.int)),
                                       GoLean.GoCore.Stmt.returnStmt]])
                               (GoLean.GoCore.Stmt.seqn #[]),
                             GoLean.GoCore.Stmt.seqn
                               #[GoLean.GoCore.Stmt.assign
                                   (GoLean.GoCore.Assignee.var "$res0")
                                   (GoLean.GoCore.Expr.intLit 0 (GoLean.GoCore.IntKind.int)),
                                 GoLean.GoCore.Stmt.returnStmt]],
                 variadic := false,
                 wrapper := false }],
    methods := #[],
    globals := #[],
    methodSets := #[{ key := "struct{}", coverage := GoLean.GoCore.MethodSetCoverage.full }] }

/-- The driver statement — the R1 differential row's subject, and the
statement the designated pair is about. -/
abbrev compareNilDriver : Stmt :=
  .call #[.var "r"] ⟨"goleanTestCompareNilToNil"⟩ #[]

end SemanticsNil

namespace ChannelActris

/-! ## The dsp row's subjects (ex-GooseParityChannels) -/

abbrev dspDriver : Stmt := .call #[.var "r"] ⟨"goleanDSPExample"⟩ #[]

abbrev dspEnv : LocalEnv := [[("r", .base ⟨0⟩)]]
abbrev dspSeed : ExecState := chanSeed actrisLowered intCell0

end ChannelActris

end GoLean.ImportedGoose
