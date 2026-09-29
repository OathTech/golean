import GoLean.GoCore.Syntax

/-!
# `ProgramCtx` — the immutable half of the machine state (B7, 2026-09-17)

The five tables `ExecState` used to carry beside the heap (`types`,
`functions`, `methods`, `methodSets`, `typeDisplays`) never change during a
run: they are the decoded `Program`, copied verbatim at setup. B7 makes the
type say so — the context is ONE record wrapping the program (D2 (b), [USER]
2026-09-16, relayed: «Yes, let's go ahead with the D1-8 rulings as
recommended»), read by every transition and written by none, so the
well-formedness network no longer re-proves at every step that the program
did not change (`docs/2026-09-16_b7-context-store-charter.md` §1).

Provenance: copied by hand from the previous build's snapshot
`85f9abd7:GoLean/GoCore/ProgramCtx.lean` (never merged), MINUS its
`platform : Platform := gcAmd64` field — D1 (a) keeps `Platform` the A5
global constant (`Platform.lean`); threading it is a later all-at-once
re-envelope lane. `ofTables` is new: the hand-built entry that mirrors the
old `ExecState` field defaults exactly (every table `#[]` — fail closed:
no method-set record → refuse every carrier query; no display record →
the visible marker), so hand-built fixtures and `runFunctionWithContextM`
keep their byte-identical behaviour. The context carries no admission
assumption: the driver seams' explicit checks (reserved prefix, arity,
`StateWf` after seeding) stay where they are.
-/

namespace GoLean.GoCore

/-- Immutable inputs shared by every transition of a program execution:
the decoded program, whole (`Program.globals` is read once by `seedGlobals`
and is merely reachable afterwards). -/
structure ProgramCtx where
  program : Program
  deriving Repr, BEq

/-- The type table (`Program.typeDefs`): dependency-ordered, index-keyed (C2). -/
def ProgramCtx.types (ctx : ProgramCtx) : TypeEnv := ctx.program.typeDefs
/-- The function table (`Program.funcs`); bodies enter the configuration at `enterFrame`. -/
def ProgramCtx.functions (ctx : ProgramCtx) : Array Func := ctx.program.funcs
def ProgramCtx.methods (ctx : ProgramCtx) : Array MethodInfo := ctx.program.methods
/-- Method-set records (contract note `docs/2026-08-10_method-set-record-contract.md`):
satisfaction and dispatch answer ONLY from these; `#[]` = refuse every carrier query. -/
def ProgramCtx.methodSets (ctx : ProgramCtx) : Array MethodSetRecord := ctx.program.methodSets
/-- Promotion records (G-P, `docs/2026-09-28_gp-method-promotion-design.md` §4): the
decoder-validated embedded-hop paths of every promoted method-set entry. Data only in
S1 (no machine consumer yet); `ofTables` leaves it `#[]`. -/
def ProgramCtx.promotions (ctx : ProgramCtx) : Array Promotion := ctx.program.promotions
/-- Display records (design note 2026-09-05 §3): gc's type string per `TypeId`, for
panic-text RENDERING only; a missing record renders the visible marker, never the key. -/
def ProgramCtx.typeDisplays (ctx : ProgramCtx) : Array (TypeId × TypeDisplay) :=
  ctx.program.typeDisplays
def ProgramCtx.globals (ctx : ProgramCtx) : Array GlobalDef := ctx.program.globals

/-- A context from bare tables, with the OLD `ExecState` defaults (every table
empty — NOT `Program`'s decoded-wire defaults `TypeEnv.reserved`/
`TypeEnv.reservedDisplays`): the hand-built entry. A fixture that needs
`struct{}` or the runtime-error payload type states `TypeEnv.reserved`
itself, as it did before B7. -/
def ProgramCtx.ofTables (types : TypeEnv := #[]) (functions : Array Func := #[])
    (methods : Array MethodInfo := #[]) (methodSets : Array MethodSetRecord := #[])
    (typeDisplays : Array (TypeId × TypeDisplay) := #[])
    (promotions : Array Promotion := #[]) : ProgramCtx :=
  ⟨{ typeDefs := types, funcs := functions, methods, globals := #[], methodSets, typeDisplays,
     promotions }⟩

@[simp] theorem ProgramCtx.ofTables_types (types : TypeEnv) (functions : Array Func)
    (methods : Array MethodInfo) (methodSets : Array MethodSetRecord)
    (typeDisplays : Array (TypeId × TypeDisplay)) :
    (ProgramCtx.ofTables types functions methods methodSets typeDisplays).types = types := rfl
@[simp] theorem ProgramCtx.ofTables_functions (types : TypeEnv) (functions : Array Func)
    (methods : Array MethodInfo) (methodSets : Array MethodSetRecord)
    (typeDisplays : Array (TypeId × TypeDisplay)) :
    (ProgramCtx.ofTables types functions methods methodSets typeDisplays).functions = functions := rfl

end GoLean.GoCore
