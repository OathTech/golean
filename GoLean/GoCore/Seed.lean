import GoLean.GoCore.StepFn
import GoLean.GoCore.StateWf

/-!
# The seeded-heap entry — function-level runs over a pre-built heap (gc-verified's a2)

[AGENT worker, lane `core/seeded-heap-a-1012`] 2026-10-12, slice A of the design note
`docs/2026-10-09_seeded-heap-design.md` ([USER] Mike 2026-10-12: GO, three slices; D4: no runtime
`StateWf` re-assert — the theorem `seedCells_wf` is the check; gc-verified confirmed the six
deviations and the v1 value set the same day, `docs/2026-10-12_seeded-heap-note-to-gc-verified.md`).

NON-SEMANTIC: `stepFn`, the relation, the drivers' loops and every pinned statement are untouched.
This module adds a DRIVER ENTRY beside `runProgramSetupM` (`runProgramSetupSeededM`), a run with a
seeded readout (`runProgramSeededM`), the seed-relative rendering helper (`seedRelative?`) and the
seed data types. The pool twin (`runProgramPoolSeededOutM`) is `SeedPool.lean` (it needs `Multi`).

Placement (design §2, D1): the seed cells are allocated AFTER `runPkgInitM` and BEFORE `bindParams`,
from the post-init allocator bound `b = s₁.heap.size` (init may allocate, so `b` is a run quantity):
the core takes seed-RELATIVE values and resolves them here. Two phases: every cell's zero value is
allocated first (cell `k` at `.base ⟨b + k⟩`, the `seedGlobals` mold with the same address check),
then every cell's value is stored at its root (`storeLoc` normalizes at the declared type), so sharing
and cycles between cells are plain stores. A `ref j path` at an expected `*T` is resolved against the
DECLARED type of cell `j` walked along `path` (`seedPathLoc`): the leaf type must be `T` (`Ty.eqb`,
positional `.defined` identity) and the location is built root-first — exactly the `Loc` the
machine's own `&c.f[i]` evaluates to. A refusal anywhere discards the WHOLE setup (an `Except`), so no
partially seeded store is ever run; references and `nil` arguments are checked against the seed's
declared types (the design's P3 found today's `bindParams` accepting a dangling address — closed here
for `.ref`/`.nil`; a SCALAR argument passes unchecked by D5, the CLI's guard, which is why S5's
bound-store statement carries the loc-free-scalar premise).

v1 (D9): int, bool, struct, array, ref, nil. Anything else — a string or float leaf, a slice, map,
channel, function, interface or sync type anywhere a value is resolved — is refused BY NAME as «not in
golean-seed-v1» at the leaf where it would be needed (the type-admission check of design §3 is this
refusal: a struct with a string field is unseedable because its required field cannot be given).
Integers are RANGE-CHECKED at their kind (no silent wrap — the normalizer would wrap); struct values
name every declared field, each exactly once, no zero-fill (D3); arrays have the exact length.

Refusals are the driver-input class (`Stop.stuck`, prefixed `seed: cell k:` / `seed: argument i:`),
the `runProgramSetupM` lookup/arity precedent: a bad seed is neither Go behaviour nor a frontend bug.

The statements S1–S6 are `SetupStatement.lean` (`SetupSound.lean` proves them; `BridgeSet.lean`
RE-PIN 18 pins them, rows added only; RE-PIN 19 re-pins the three S6 rows for the readout's
`base`, below). The raw `Store.alloc`/`storeLoc` sites here are in
`scripts/mem-callsites.tsv` (FRESH ALLOCATION: the seed cells are created at setup — zero-allocated,
then filled — before any step runs; no access is emitted).
-/

namespace GoLean.GoCore.Machine

open GoLean

/-- One step of a seed path, from the cell's root outwards. -/
inductive SeedPathElem where
  | field (name : String)
  | index (i : Nat)
  deriving Repr, BEq, DecidableEq

/-- A seed value, seed-RELATIVE: `ref` names a cell by its index in the seed and a path into it;
`struct` names its fields (D3; order irrelevant, every declared field required). The recursive
positions are `List`s (kernel-reducible structural recursion; the JSON shape is the CLI's). -/
inductive SeedValue where
  | int (v : Int)
  | bool (b : Bool)
  | struct (fields : List (String × SeedValue))
  | array (elems : List SeedValue)
  | ref (cell : Nat) (path : List SeedPathElem)
  | nil
  deriving Repr, Inhabited

/-- A seed cell: its declared type and its value. -/
structure SeedCell where
  typ : Ty
  value : SeedValue
  deriving Repr, Inhabited

/-- An entry argument over a seed: a scalar (checked by the CLI's `entryArgValues`, as today —
unchecked here, D5), a reference into the seed, or `nil` at a pointer parameter. -/
inductive SeedArg where
  | scalar (v : GoValue)
  | ref (cell : Nat) (path : List SeedPathElem)
  | nil
  deriving Repr, Inhabited

/-! ## Resolution: seed-relative values to machine values at a declared type -/

/-- `v` is representable at integer kind `kind` WITHOUT wrapping (the normalizer wraps; a seed value
outside the kind's range is refused, never wrapped). Untyped kinds never name a declared type. -/
def seedIntFits (kind : IntKind) (v : Int) : Bool :=
  match kind.bits? with
  | none => false
  | some bits =>
      if kind.signed then -((2 : Int) ^ (bits - 1)) ≤ v && v < (2 : Int) ^ (bits - 1)
      else 0 ≤ v && v < (2 : Int) ^ bits

/-- Walk `path` from a location `loc` of declared type `ty`, root-first: `.field f` needs a struct
body with field `f` (through `.defined`), `.index i` an array with `i < length`. Returns the leaf
location and its declared type. Structural on the path; `.defined` chains resolve through the table
with `TypeEnv.resolve` (bounded by the table size, total on any table). -/
def seedPathLoc (types : TypeEnv) : Loc → Ty → List SeedPathElem → Except Stop (Loc × Ty)
  | loc, ty, [] => .ok (loc, ty)
  | loc, ty, .field f :: rest =>
      match TypeEnv.resolve types types.size ty with
      | .error e => .error e
      | .ok (.struct name fields) =>
          match fields.find? (·.name == f) with
          | some d => seedPathLoc types (.field loc name f) d.typ rest
          | none => stuck s!"unknown field {f} of {name.key}"
      | .ok _ => stuck s!"path .{f} on a non-struct type"
  | loc, ty, .index i :: rest =>
      match TypeEnv.resolve types types.size ty with
      | .error e => .error e
      | .ok (.plain (.array n e)) =>
          if i < n then seedPathLoc types (.index loc i) e rest
          else stuck s!"index {i} out of range for an array of length {n}"
      | .ok _ => stuck s!"path [{i}] on a non-array type"

/-- The declared type of cell `j` (`.error` when `j` is out of range), as the root of a reference. -/
def seedCellTy (seed : Array SeedCell) (j : Nat) : Except Stop Ty :=
  match seed[j]? with
  | some c => .ok c.typ
  | none => stuck s!"ref to cell {j} out of range ({seed.size} cells)"

/-- A seed path rendered as the design writes it: `0`, `0.next`, `1[2]`, `0.a[3].b`. -/
def renderSeedPath (j : Nat) (path : List SeedPathElem) : String :=
  toString j ++ String.join (path.map fun | .field f => s!".{f}" | .index i => s!"[{i}]")

/-- Resolve a reference `ref j path` expected at pointer type `*target` (the pointee type `target`):
the cell exists, the path is declared, the leaf type IS `target`. -/
def resolveSeedRef (types : TypeEnv) (b : Nat) (seed : Array SeedCell) (target : Ty)
    (j : Nat) (path : List SeedPathElem) : Except Stop GoValue := do
  let root ← seedCellTy seed j
  let (loc, leaf) ← seedPathLoc types (.base ⟨b + j⟩) root path
  if Ty.eqb leaf target then pure (.addr loc)
  else stuck s!"ref {renderSeedPath j path} has type *{Ty.dynamicName types.nameOf? leaf}, *{Ty.dynamicName types.nameOf? target} expected"

/-- Reorder resolved struct fields into DECLARED order, requiring every declared field exactly once
(no zero-fill, no duplicates; an unknown name was refused when it was resolved). -/
def seedStructOrder (name : TypeId) : List FieldDef → List (String × GoValue) →
    Except Stop (List (String × GoValue))
  | [], _ => .ok []
  | d :: ds, given =>
      if d.name == "_" then
        stuck s!"struct {name.key}: a blank field (_) cannot be seeded (not in golean-seed-v1)"
      else
      match given.filter (·.1 == d.name) with
      | [(_n, v)] => do
          let rest ← seedStructOrder name ds given
          pure ((d.name, v) :: rest)
      | [] => stuck s!"struct {name.key}: missing field {d.name}"
      | _ => stuck s!"struct {name.key}: duplicate field {d.name}"

mutual
/-- Resolve a seed value at declared type `ty` over the seed's base `b`: the machine value, normal
at `ty` by construction (ints range-checked, fields in declared order, arrays exact), or a named
refusal. -/
def resolveSeedValue (types : TypeEnv) (b : Nat) (seed : Array SeedCell) (ty : Ty) :
    SeedValue → Except Stop GoValue
  | .int v =>
      match TypeEnv.resolve types types.size ty with
      | .error e => .error e
      | .ok (.plain (.int kind)) =>
          if seedIntFits kind v then .ok (.int v kind)
          else stuck s!"int {v} out of range for {kind.name}"
      | .ok _ => stuck s!"int value at type {Ty.dynamicName types.nameOf? ty} — an integer type expected"
  | .bool x =>
      match TypeEnv.resolve types types.size ty with
      | .error e => .error e
      | .ok (.plain .bool) => .ok (.bool x)
      | .ok _ => stuck s!"bool value at type {Ty.dynamicName types.nameOf? ty} — bool expected"
  | .struct fields =>
      match TypeEnv.resolve types types.size ty with
      | .error e => .error e
      | .ok (.struct name decl) => do
          let given ← resolveSeedFields types b seed name decl fields
          let ordered ← seedStructOrder name decl.toList given
          pure (.struct name ordered.toArray)
      | .ok _ => stuck s!"struct value at type {Ty.dynamicName types.nameOf? ty} — a declared struct type expected"
  | .array elems =>
      match TypeEnv.resolve types types.size ty with
      | .error e => .error e
      | .ok (.plain (.array n e)) =>
          if elems.length != n then
            stuck s!"expected array({n}), got {elems.length} element(s)"
          else
            (resolveSeedList types b seed e elems).map (fun vs => .array vs.toArray)
      | .ok _ => stuck s!"array value at type {Ty.dynamicName types.nameOf? ty} — an array type expected"
  | .ref j path =>
      match TypeEnv.resolve types types.size ty with
      | .error e => .error e
      | .ok (.plain (.pointer target)) => resolveSeedRef types b seed target j path
      | .ok _ => stuck s!"ref at type {Ty.dynamicName types.nameOf? ty} — a pointer type expected"
  | .nil =>
      match TypeEnv.resolve types types.size ty with
      | .error e => .error e
      | .ok (.plain (.pointer _)) => .ok .nil
      | .ok _ => stuck s!"nil at non-pointer type {Ty.dynamicName types.nameOf? ty} (v1: nil only at pointer types)"

/-- The elements of an array value, in order, at the element type. -/
def resolveSeedList (types : TypeEnv) (b : Nat) (seed : Array SeedCell) (elem : Ty) :
    List SeedValue → Except Stop (List GoValue)
  | [] => .ok []
  | v :: vs => do
      let w ← resolveSeedValue types b seed elem v
      let ws ← resolveSeedList types b seed elem vs
      pure (w :: ws)

/-- The given fields of a struct value, each at ITS declared field type (an unknown field name
refuses); the declared order and the completeness check are `seedStructOrder`'s. -/
def resolveSeedFields (types : TypeEnv) (b : Nat) (seed : Array SeedCell) (name : TypeId)
    (decl : Array FieldDef) : List (String × SeedValue) → Except Stop (List (String × GoValue))
  | [] => .ok []
  | (f, v) :: rest =>
      match decl.find? (·.name == f) with
      | none => stuck s!"struct {name.key}: unknown field {f}"
      | some d => do
          let w ← resolveSeedValue types b seed d.typ v
          let ws ← resolveSeedFields types b seed name decl rest
          pure ((f, w) :: ws)
end

/-- An entry argument at the parameter's declared type: a scalar passes UNCHECKED (D5 — the CLI's
`entryArgValues` guards it, as today, which keeps the empty-seed erasure S4 unconditional); a
reference or `nil` resolves exactly like a seed value at that type. -/
def resolveSeedArg (types : TypeEnv) (b : Nat) (seed : Array SeedCell) (ty : Ty) :
    SeedArg → Except Stop GoValue
  | .scalar v => .ok v
  | .ref j path => resolveSeedValue types b seed ty (.ref j path)
  | .nil => resolveSeedValue types b seed ty .nil

/-- Mark a refusal with the argument position it belongs to (the `markInitPhase` shape: the three
diagnostic classes; `panic`/`fuelOut` carry no text). -/
def markSeedArg (i : Nat) : Stop → Stop
  | .stuck msg => .stuck s!"seed: argument {i}: {msg}"
  | .unsupported msg => .unsupported s!"seed: argument {i}: {msg}"
  | .internal msg => .internal s!"seed: argument {i}: {msg}"
  | e => e

/-- Mark a refusal with the cell it belongs to. -/
def markSeedCell (k : Nat) : Stop → Stop
  | .stuck msg => .stuck s!"seed: cell {k}: {msg}"
  | .unsupported msg => .unsupported s!"seed: cell {k}: {msg}"
  | .internal msg => .internal s!"seed: cell {k}: {msg}"
  | e => e

/-- The arguments against the parameter list, positionally (arity is checked by the entry before). -/
def resolveSeedArgsList (types : TypeEnv) (b : Nat) (seed : Array SeedCell) :
    Nat → List Param → List SeedArg → Except Stop (List GoValue)
  | _, [], [] => .ok []
  | i, p :: ps, a :: as => do
      let v ← (resolveSeedArg types b seed p.typ a).mapError (markSeedArg i)
      let vs ← resolveSeedArgsList types b seed (i + 1) ps as
      pure (v :: vs)
  | _, _, _ => stuck "seed: argument count does not match the parameter list"

/-- The resolved argument values of the entry (design §2, `resolveSeedArgs`). -/
def resolveSeedArgs (types : TypeEnv) (b : Nat) (seed : Array SeedCell) (params : Array Param)
    (args : Array SeedArg) : Except Stop (Array GoValue) :=
  (resolveSeedArgsList types b seed 0 params.toList args.toList).map List.toArray

/-! ## The two-phase allocation -/

variable (ctx : ProgramCtx)

/-- Phase 1 from cell `k`: the zero cell of each declared type, allocated in order; the allocator's
address is checked against `.base ⟨b + k⟩` (the `seedGlobals` mold; provably never fires —
`seedCells_locs`). -/
def seedAllocFrom (b : Nat) : Store → Nat → List SeedCell → Except Stop Store
  | s, _, [] => .ok s
  | s, k, c :: rest => do
      let z ← (defaultValue ctx c.typ).mapError (markSeedCell k)
      let (loc, s') ← Store.alloc ctx s z c.typ
      if loc != .base ⟨b + k⟩ then
        throw (.internal s!"seed: cell {k} allocated at {repr loc}, expected base {b + k}")
      seedAllocFrom b s' (k + 1) rest

/-- Phase 2 from cell `k`: each cell's value, resolved against the seed, stored at its root (the
whole-root write normalizes at the declared type; every cell already exists, so references
between cells — sharing, cycles — are plain stores). -/
def seedStoreFrom (b : Nat) (seed : Array SeedCell) : Store → Nat → List SeedCell → Except Stop Store
  | s, _, [] => .ok s
  | s, k, c :: rest => do
      let v ← (resolveSeedValue ctx.types b seed c.typ c.value).mapError (markSeedCell k)
      let s' ← storeLoc ctx s (.base ⟨b + k⟩) v
      seedStoreFrom b seed s' (k + 1) rest

/-- The seed's slots: cell `k` at `.base ⟨b + k⟩` (`entrySlot s₁ k` for `b = s₁.heap.size`). -/
def seedLocs (b n : Nat) : Array Loc :=
  ((List.range n).map (fun k => Loc.base ⟨b + k⟩)).toArray

/-- The seeded store over the post-init store `s₁`: phase 1 then phase 2 from
`b = s₁.heap.size`, and the slot list. -/
def seedCells (s₁ : Store) (seed : Array SeedCell) : Except Stop (Store × Array Loc) := do
  let b := s₁.heap.size
  let sA ← seedAllocFrom ctx b s₁ 0 seed.toList
  let sS ← seedStoreFrom ctx b seed sA 0 seed.toList
  return (sS, seedLocs b seed.size)

/-! ## The entries -/

/-- The seeded whole-PROGRAM entry: `runProgramSetupM`'s steps VERBATIM through `runPkgInitM`
(find → arity → reserved prefix → `seedGlobals` → the `StateWf` assert → init), then the seed
cells from the post-init bound, the arguments resolved against the parameters, then parameter
binding, result allocation and pinning and the entry configuration exactly as today. The seed
slots are returned beside the result locations (the readout reads the cells' final values). No
`StateWf` re-assert after seeding (D4): `seedCells_wf` is that check, as a theorem. -/
def runProgramSetupSeededM (fuel : Nat) (program : Program) (name : String)
    (seed : Array SeedCell) (args : Array SeedArg) (choices : Choices := []) :
    Except Stop (ProgramCtx × Config × Store × List Loc × Array Loc × Choices) := do
  let func ←
    match findFunctionIn? program.funcs ⟨name⟩ with
    | some func => pure func
    | none => throw (.stuck s!"GoCore function not found: {name}")
  if func.args.size != args.size then
    throw (.stuck s!"expected {func.args.size} argument(s), got {args.size}")
  if program.typeDefs.hasReservedPrefix then pure () else
    throw (.internal s!"program type table does not lead with the two machine-reserved entries ({emptyStructTypeId.key} at index 0, {runtimeErrorTypeId.key} at index 1): TypeEnv.hasReservedPrefix fails on a {program.typeDefs.size}-entry table — prepend TypeEnv.reserved (C2 acceptance clause)")
  let pctx : ProgramCtx := ⟨program⟩
  let state : Store := {}
  let s₀ ← seedGlobals pctx state program.globals
  if StateWf pctx s₀ then pure () else
    throw (.internal "seeded state ill-formed: a location in a global cell dangles beyond the allocator bound")
  let (s₁, choices₁) ← runPkgInitM pctx fuel s₀ choices
  let (sS, slots) ← seedCells pctx s₁ seed
  let vals ← resolveSeedArgs pctx.types s₁.heap.size seed func.args args
  let (env, s₂) ← bindParams pctx [] sS func.args.toList vals.toList
  let (frameEnv, s₃) ← allocDecls pctx env s₂ func.results.toList
  let resultLocs ← pinResultLocs frameEnv func.results.toList
  let c₀ : Config := .exec func.body frameEnv (.frame [] [] [] [] .stop func.id)
  return (pctx, c₀, s₃, resultLocs, slots, choices₁)

/-- The seeded readout: the ordinary readout, the seed's BASE `b` (the post-init allocator bound
the cells were placed from — cell `k` is `.base ⟨base + k⟩`, so `seedFinal[k]` is the final
content of that cell), and the seed cells' FINAL values (raw machine values — the seed-relative
rendering and its refusal live in the observation layer, over `seedRelative? base seedFinal.size`;
design §5, deviation (e)).

`base` was added by RE-PIN 19 ([AGENT worker, lane `core/seeded-base-repin-1012`], 2026-10-12;
[USER] Mike 2026-10-12 approved items 1 and 3-6 of that ask; item 6 proposed carrying the seed
base in the core readout, changing BridgeSet rows 599 to 601 — a customer-visible re-pin to
notice to the logic team; relayed by the [AGENT] coordinator): without it the CLI re-ran `runProgramSetupSeededM` after
the run to learn `b` from slot 0 — package init twice per seeded run (slice B's debt, review
LOW-2). `b` is a RUN quantity (init may allocate), known only inside the setup; it travels as a
`Nat` rather than the slot list because that list IS `seedLocs b n` (S2 `seedCells_locs`), one
number spelled `n` times, and the renderer consumes the number. -/
structure SeededReadout where
  readout : Readout
  base : Nat
  seedFinal : Array GoValue
  deriving Repr, BEq

/-- The seed's base from the setup's slot list (the setup returns the slots, S1; its tuple is
pinned, so the base is read off it): slot 0 is `.base ⟨b⟩` (`seedCells_locs`), and an EMPTY seed
has no slot and nothing to be relative to — its base is 0, the canonical don't-care
(`seedRelative? b 0 l = none` at every `b`; the erasure statements spell it). A slot that is not
a base address cannot arise (S2) and is refused by name rather than guessed. -/
def seedBase (slots : Array Loc) : Except Stop Nat :=
  match slots[0]? with
  | none => .ok 0
  | some (Loc.base a) => .ok a.id
  | some _ => .error (.internal "seed: slot 0 is not a base address")

/-- The seeded run on the sequential driver: the seeded setup, the base read off its slots,
`runConfig`, the results, the final seed cells. -/
def runProgramSeededM (fuel : Nat) (program : Program) (name : String)
    (seed : Array SeedCell) (args : Array SeedArg) (choices : Choices := []) :
    Except Stop SeededReadout := do
  let (pctx, c₀, s₃, resultLocs, slots, choices₁) ←
    runProgramSetupSeededM fuel program name seed args choices
  let base ← seedBase slots
  let (sF, _) ← runConfig pctx fuel s₃ c₀ choices₁
  let values ← loadMany pctx sF resultLocs
  let finals ← loadMany pctx sF slots.toList
  return { readout := { values := values.toArray }, base := base, seedFinal := finals.toArray }

/-! ## Seed-relative rendering -/

/-- A location INSIDE the seed (`b ≤ root < b + n`; `b` is the readout's `base`, `n` its
`seedFinal.size`), as the cell index and the path from its root (`.field _ f ↦ .field f`,
`.index i ↦ .index i`; a negative index is not a seed path). `none` for a location outside the
seed — the observation layer refuses the whole observation by name there. -/
def seedRelative? (b n : Nat) (l : Loc) : Option (Nat × List SeedPathElem) :=
  let (a, path) := Loc.rootPath l
  if b ≤ a.id && a.id < b + n then
    (path.mapM fun (step : PathStep) =>
      match step with
      | .field _ f => some (SeedPathElem.field f)
      | .index i => if i < 0 then none else some (SeedPathElem.index i.toNat)).map (fun p => (a.id - b, p))
  else none

end GoLean.GoCore.Machine
