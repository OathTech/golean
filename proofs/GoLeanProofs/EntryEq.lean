import Lean
import GoLean.GoCore.MachineSound

/-!
# `derive_entry_eq` — the entry-equation macro (phase-2 slice 2, P4;
2026-08-14)

Every harness proof module opens with the same ~15–30-line dance: a
hand-derived post-prelude `ExecState` def (argument cells normalized at
their declared types, result cells at their defaults, `nextAddr`
counted), a start `Config` def (the body under the entry barrier
frame), and "the entry equation" — a theorem equating
`runFunctionWithContextM` on the pinned harness `Func` at symbolic
arguments with its `runConfig` form from that state, closed by
`with_unfolding_all rfl`. Ten modules carry the pattern
(`fibH_entry_eq`, `gcdh_entry_eq`, `mmh_entry_eq`, `rH_entry_eq` ×2,
`revH(V)_entry_eq` ×2, `wcH_entry_eq`, `iharness_entry_eq`,
`harness_entry_eq`). This command derives all three declarations from
the program and the `Func` in one invocation:

```
derive_entry_eq fibH_entry_eq fibLowered fibHarnessFunc fibHSeed fibHC₀
```

(argument order: theorem name, lowered-program constant, harness
`Func` constant, then the NAMES to emit for the state and start-config
defs — the module's own names, so downstream lemmas keep their
spelling)

emits (in the caller's namespace, so downstream segment lemmas keep
their spelling — the state/cont names are the module's own):

* `def fibHSeed (n : Int) : ExecState` — the post-prelude state; its
  arguments are the ALREADY-normalized parameter values, exactly the
  hand-written convention;
* `def fibHC₀ : Config` — the body under `.frame [] [] [] [] .stop`;
* `theorem fibH_entry_eq (n : Int) (fuel : Nat) (ch : Choices) : … `
  — the entry equation at fully symbolic arguments/fuel/choices,
  proved by `with_unfolding_all rfl`.

The layout is COMPUTED, not probed: parameter cells at addresses
`0…p−1` (the `bindParams` order), result cells at `p…p+r−1` at their
`defaultValue`s (the `allocDecls` order), one scope in
reverse-declaration order, result locations in declaration order —
mirroring `runFunctionWithContextM`'s prelude by construction.

## Untrusted method, twice over

The macro is proof-side tooling: it GENERATES declarations that the
elaborator and kernel then check like any hand-written ones — nothing
here is trusted, no gate consumes it, and no emitted name may enter a
headline statement closure (form note §12b; the entry equation is §11
GLUE, below the statement layer). The meta-level evaluation inside
(computing the layout and the validity probe) can at worst make the
macro emit a false statement — which the final `rfl` then refuses.

## The `#eval`-before-`decide` guard, mechanized

A FALSE entry equation handed to `with_unfolding_all rfl` is the
known 60 GB failure mode (CLAUDE.md: a decision procedure that must
reduce to `False` has no reason to terminate politely). So before
emitting the theorem, the macro EVALUATES the derived equation at ONE
concrete probe point (all arguments `1`, generous fuel, empty choice
stream) with the compiler — cheap — in two steps: it first requires
the machine-entry run to be `.ok` there, and then requires both sides
to agree, reporting them if they differ. The `.ok` step is not
decoration (pre-merge audit, 2026-08-15): without it two runs that
both end in `.error .fuelOut` compare EQUAL, and the guard would
certify an equation on a run that never happened.

What the guard does and does not buy, stated honestly: it is a
SINGLE-POINT check of a statement that is symbolic in the arguments,
the fuel and the choice stream. A layout wrong AT the probe point —
the failure mode a mis-derived prelude actually produces, since the
layout is argument-independent — fails loudly in milliseconds instead
of in the kernel. A divergence that only appears away from the probe
point would still reach `with_unfolding_all rfl`, which refuses it,
expensively. The guard shortens the common failure; it does not
remove the kernel as the thing that decides.

## Fail-closed scope (extend deliberately, never silently)

Covers exactly the shape every current harness entry has: ≥1
parameters, ALL of scalar integer type (`.int k`); result defaults
quoted for scalar values, arrays OF scalars, nil slices/maps. Anything
else — float/chan/struct/interface parameters, nested aggregate
defaults, variadic entry — is a hard elaboration error naming the
unsupported piece. Widen the quoters when a real harness needs it.

## PUBLIC API — the sealed interface (the W6 convention, as in
`StepKit`/`SliceMem`; section added WP arc s3, 2026-08-18)

This module's public surface is a COMMAND, not a lemma family, so the
contract is shaped differently from its siblings — but the same rule
holds: consumers depend on what is listed here and nothing else.

**Group 1 — the command** (the whole intended API):
`derive_entry_eq <thm> <prog> <func> <stateName> <contName> [<base>]`.
Its contract is the three declarations it emits IN THE CALLER'S
NAMESPACE under the caller's chosen names (the state `def`, the start
`Config` `def`, the entry-equation `theorem`), the computed layout
above, and the fail-closed scope above. Consumers name the emitted
declarations, never anything in this module.

**Group 2 — the meta plumbing** (public because Lean's elaborator
needs it; NOT a consumer surface, and spelling may change):
`EntryLayout`, `computeEntryLayout`, the `opaque`/`unsafe` evaluation
pairs `evalLayout`/`evalLayoutUnsafe` and `evalBool`/`evalBoolUnsafe`,
the quoters `quoteIntKind`,
`quoteScalarTy`, `quoteTy`, `quoteScalarVal`, `quoteVal`, `quoteLoc`,
`binderIdentFor`, and the elaborator `elabDeriveEntryEq`. Treat this
group as `private`-by-contract: it is public only because
`unsafe`/`CommandElab` declarations cannot be hidden and still be
wired up.

**The API discipline**:

1. Everything here is UNTRUSTED METHOD, twice over (see above): the
   macro emits declarations the elaborator and kernel check like any
   hand-written ones, and no emitted name may enter a headline
   statement closure (§12b; the entry equation is §11 GLUE).
2. The emitted THEOREMS carry `#print axioms` pins in
   `Audit/Kit.lean` § the `derive_entry_eq` emitted-theorem fixtures
   — the pins live on the fixtures, not on this module's meta
   declarations, which have no meaningful axiom content.
3. Scope widens DELIBERATELY: a new value shape means a new quoter
   arm plus its fail-closed error, never a silent fallback.
4. This module is the kit's ONLY `escape-hatch` allowlist entry
   (`scripts/ci` meta-layer check) — the `unsafe` evaluation is
   scoped to layout/probe computation and guarded by the final `rfl`.
5. **Storm/signature discipline: StepKit rules 1–5** apply to what
   the macro EMITS: the emitted state is the fully-pinned form rule 1
   asks for, which is why the emitted entry equation is
   program-size-independent where the hand-written dances were not.

## WHAT LIVES WHERE (the kit map — WP arc s3, 2026-08-18)

THIS module: the program ENTRY — from `runFunctionWithContextM` at
symbolic arguments to a `runConfig` from a named post-prelude state.
It is the only kit module that generates code.

Siblings, and the boundary with each:

* `FuelMeasure` — the `runConfig` glue (API group 4 there) that the
  emitted entry equation hands off to; the readouts that turn the
  resulting total headline into a run-conditioned one.
* `StepKit` — `stepFn_call_enter`, the conditioned call-entry step
  the emitted equation's continuation is chained onto.
* `StringMem` — its examples' entry equations are the ones the s2
  string arm closed; the arm itself quotes only `GoString.empty` (the
  sole string default `defaultValue` produces), and the `gs`-spelled
  cells appear DOWNSTREAM, in the segments those examples chain.
* `SliceMem` / `MapMem` — the slice/map result defaults the quoters
  emit are the NIL handles (`.slice ⟨none, …⟩`, `.map ⟨none⟩`), not
  those modules' `sliceVal`/`mapVal` (which name a BACKED handle);
  the vocabulary enters later, when the harness allocates.

`docs/kit-guide.md` — THE SITUATION INDEX; read it before writing a
new proof. Section fed by this module: **Entry** (both invocation
forms, the string arm, and the fail-closed refusals).
-/

open Lean Elab Command Term Meta
open GoLean GoLean.GoCore GoLean.GoCore.Machine

namespace GoLean.Surface.EntryEq

/-! ### API group 2 — the computed layout. -/

/-- The computed entry layout: parameter names with their integer
kinds, result names with their declared types and default values. -/
structure EntryLayout where
  args : List (String × IntKind)
  results : List (String × Ty × GoValue)

/-- Compute the layout the `runFunctionWithContextM` prelude produces
for `func` — executable, evaluated at elaboration time by the macro.
Fails closed on any parameter that is not a scalar integer. -/
def computeEntryLayout (types : TypeEnv) (func : Func) :
    Except String EntryLayout := do
  if func.args.isEmpty then
    throw "derive_entry_eq covers harness entries with ≥1 parameters"
  let args ← func.args.toList.mapM (fun p =>
    match p.typ with
    | .int k => .ok (p.id, k)
    | t => .error s!"parameter '{p.id}' has non-scalar-integer type \
        {reprStr t} — derive_entry_eq covers scalar-integer entries \
        only (fail closed; widen deliberately)")
  let results ← func.results.toList.mapM (fun p => do
    match defaultValue { types := types } p.typ with
    | .ok v => .ok (p.id, p.typ, v)
    | .error e => .error s!"defaultValue failed for result \
        '{p.id}': {reprStr e}")
  return { args, results }

/-! ### API group 2 — meta plumbing: unsafe evaluation behind opaque
wrappers.
The results only ever shape SYNTAX that is then elaborated and
kernel-checked; a wrong evaluation yields a refused `rfl`, never a
wrong theorem. -/

unsafe def evalLayoutUnsafe (stx : Term) :
    TermElabM (Except String EntryLayout) := do
  let ty ← Term.elabType (← `(Except String EntryLayout))
  let e ← Term.elabTermEnsuringType stx ty
  Term.synthesizeSyntheticMVarsNoPostponing
  let e ← instantiateMVars e
  Meta.evalExpr (Except String EntryLayout) ty e

@[implemented_by evalLayoutUnsafe]
opaque evalLayout (stx : Term) : TermElabM (Except String EntryLayout)

unsafe def evalBoolUnsafe (stx : Term) : TermElabM Bool := do
  let ty := Lean.mkConst ``Bool
  let e ← Term.elabTermEnsuringType stx ty
  Term.synthesizeSyntheticMVarsNoPostponing
  let e ← instantiateMVars e
  Meta.evalExpr Bool ty e

@[implemented_by evalBoolUnsafe]
opaque evalBool (stx : Term) : TermElabM Bool

/-! ### API group 2, continued — quoters: data back to syntax, on the
fail-closed fragment. -/

def quoteIntKind : IntKind → CommandElabM Term
  | .int => `(IntKind.int)
  | .uint => `(IntKind.uint)
  | .int8 => `(IntKind.int8)
  | .uint8 => `(IntKind.uint8)
  | .int16 => `(IntKind.int16)
  | .uint16 => `(IntKind.uint16)
  | .int32 => `(IntKind.int32)
  | .uint32 => `(IntKind.uint32)
  | .int64 => `(IntKind.int64)
  | .uint64 => `(IntKind.uint64)
  | .unbounded s => throwError
      "derive_entry_eq: unbounded integer kind '{s}' cannot appear in \
       a runtime entry layout (fail closed)"

def quoteScalarTy : Ty → CommandElabM Term
  | .bool => `(Ty.bool)
  | .int k => do `(Ty.int $(← quoteIntKind k))
  | .string => `(Ty.string)
  | t => throwError
      "derive_entry_eq: type {reprStr t} is outside the quoted \
       fragment (scalar bool/int/string) — widen the quoter \
       deliberately (fail closed)"

/-- One aggregate level over scalars — exactly what harness results
use (`[N]uint64`, `[]uint64`, `map[k]v` handles). -/
def quoteTy : Ty → CommandElabM Term
  | .array n t => do `(Ty.array $(quote n) $(← quoteScalarTy t))
  | .slice t => do `(Ty.slice $(← quoteScalarTy t))
  | .map k v => do `(Ty.map $(← quoteScalarTy k) $(← quoteScalarTy v))
  | .pointer t => do `(Ty.pointer $(← quoteScalarTy t))
  | t => quoteScalarTy t

def quoteScalarVal : GoValue → CommandElabM Term
  | .unit => `(GoValue.unit)
  | .bool b => do `(GoValue.bool $(quote b))
  | .int v k => do
      if v < 0 then
        throwError "derive_entry_eq: negative default {v} outside the \
          quoted fragment (fail closed)"
      `(GoValue.int $(quote v.toNat) $(← quoteIntKind k))
  | .nil => `(GoValue.nil)
  -- WP arc s2 item 6: the STRING result-default arm — the only string
  -- default `defaultValue` can produce is the empty string, so the
  -- quoter covers exactly that point and stays fail-closed one value
  -- wider (closes the strrev/wordfreq hand-written entry dances).
  | .string ⟨#[]⟩ => `(GoValue.string GoString.empty)
  | v => throwError
      "derive_entry_eq: default value {reprStr v} is outside the \
       quoted fragment — widen the quoter deliberately (fail closed)"

def quoteVal : GoValue → CommandElabM Term
  | .array vs => do
      let elems ← vs.toList.mapM quoteScalarVal
      `(GoValue.array #[$(elems.toArray),*])
  | .slice ⟨none, o, l, c⟩ => do
      `(GoValue.slice ⟨none, $(quote o), $(quote l), $(quote c)⟩)
  | .slice sv => throwError
      "derive_entry_eq: non-nil slice default {reprStr sv} cannot \
       arise from defaultValue (fail closed)"
  | .map ⟨none⟩ => `(GoValue.map ⟨none⟩)
  | v => quoteScalarVal v

/-- A heap-address literal `Loc.base ⟨i⟩`. -/
def quoteLoc (i : Nat) : CommandElabM Term := `(Loc.base ⟨$(quote i)⟩)

/-- Lean binder identifiers for the Go parameter names (fallback
`aᵢ` when a Go name is not a plain Lean identifier). -/
def binderIdentFor (goName : String) (i : Nat) : Ident :=
  let ok := match goName.toList with
    | [] => false
    | c :: rest => c.isAlpha && rest.all (fun c => c.isAlphanum || c == '_')
  mkIdent (Name.mkSimple (if ok then goName else s!"a{i}"))

/-! ## API group 1 — THE COMMAND (the whole intended API).

Two forms (the optional trailing ident is the PROGRAM-GENERIC
extension, Gallery Campaign G0 item 3c, 2026-08-15):

```
derive_entry_eq thm prog func state cont        -- flat state def
derive_entry_eq thm prog func state cont base   -- program-generic
```

In the six-ident form, `base` names an existing `ExecState` constant —
the module's program-as-empty-heap state (the `vProg`/`rProg`
convention of the program-generic modules) — and the emitted state def
is the RECORD UPDATE `{ base with heap := …, nextAddr := … }` instead
of a flat record literal. This preserves the record-update structure
the σ-generic segment lemmas are stated over (`rSt σ H na` =
`{ σ with heap := H, nextAddr := na }`), so the consumer's one
show-bridge line between the emitted def and the module's
compositional spelling (`rSt rProg (rHeap0 …) na`) is a STRUCTURAL
`rfl` — record updates of the same base — never a whnf of the
program constant (the storm class the program-generic form exists to
avoid; slice-2 record §3's recorded show-bridge).

Fail-closed note: the macro does not separately check that `base`'s
program fields agree with `prog`'s — a mismatch makes the probe run a
DIFFERENT program on the `runConfig` side, so the probe (or, past the
probe point, the final `rfl`) refuses. -/

syntax (name := deriveEntryEq)
  "derive_entry_eq " ident ident ident ident ident (ident)? : command

@[command_elab deriveEntryEq]
def elabDeriveEntryEq : CommandElab := fun stx => do
  match stx with
  | `(command| derive_entry_eq $thmId $progId $funcId $stateId $contId
        $[$baseId?]?) => do
    -- 1. Compute the layout (compiler evaluation of the executable
    --    `computeEntryLayout` at the caller's program + Func).
    let layoutStx ← `(GoLean.Surface.EntryEq.computeEntryLayout
      ($progId).typeDefs.toList $funcId)
    let layout ← liftTermElabM (evalLayout layoutStx)
    let layout ← match layout with
      | .ok l => pure l
      | .error e => throwError "derive_entry_eq: {e}"
    let p := layout.args.length
    let binders := (layout.args.zipIdx.map
      (fun ((nm, _), i) => binderIdentFor nm i)).toArray
    let binderF : TSyntaxArray [`ident, `Lean.Parser.Term.hole] :=
      binders.map (fun b => ⟨b.raw⟩)
    let kinds ← layout.args.mapM (fun (_, k) => quoteIntKind k)
    let kinds := kinds.toArray
    -- 2. The state def: argument cells 0…p−1 (values = the binders,
    --    i.e. already normalized at the call site), result cells at
    --    their defaults, nextAddr = p + r.
    let mut heapItems : Array Term := #[]
    for ((_, k), i) in layout.args.zipIdx do
      let kT ← quoteIntKind k
      let loc ← quoteLoc i
      let b := binders[i]!
      heapItems := heapItems.push
        (← `(($loc, ⟨some (Ty.int $kT), GoValue.int $b $kT⟩)))
    for ((_, ty, v), j) in layout.results.zipIdx do
      let loc ← quoteLoc (p + j)
      let tyT ← quoteTy ty
      let vT ← quoteVal v
      heapItems := heapItems.push (← `(($loc, ⟨some $tyT, $vT⟩)))
    let heapT ← `([$heapItems,*])
    let na := quote (p + layout.results.length)
    match baseId? with
    | some baseId =>
      -- Program-generic form: a record update of the caller's
      -- program-as-empty-heap base state, so σ-generic segment
      -- machinery bridges structurally (module docstring above).
      elabCommand (← `(command|
        /-- The machine entry's post-prelude state (derived by
        `derive_entry_eq`, program-generic form): the base state with
        argument cells at `0…p−1` — this def receives the
        ALREADY-normalized parameter values — and result cells at
        their defaults after them. -/
        def $stateId ($binderF* : Int) : ExecState :=
          { $baseId with heap := $heapT, nextAddr := $na }))
    | none =>
      elabCommand (← `(command|
        /-- The machine entry's post-prelude state (derived by
        `derive_entry_eq` from the pinned lowering): argument cells at
        `0…p−1` — this def receives the ALREADY-normalized parameter
        values — result cells at their defaults after them. -/
        def $stateId ($binderF* : Int) : ExecState :=
          { types := ($progId).typeDefs.toList,
            functions := ($progId).funcs,
            methods := ($progId).methods,
            heap := $heapT,
            nextAddr := $na }))
    -- 3. The start configuration: one scope, reverse-declaration
    --    order (params then results, `LocalEnv.declare` conses).
    let allNames := layout.args.map (·.1) ++ layout.results.map (·.1)
    let mut scopeItems : Array Term := #[]
    for (nm, i) in allNames.zipIdx.reverse do
      let loc ← quoteLoc i
      scopeItems := scopeItems.push (← `(($(quote nm), $loc)))
    let envT ← `(([[$scopeItems,*]] : LocalEnv))
    elabCommand (← `(command|
      /-- The post-prelude start configuration (derived by
      `derive_entry_eq`): the harness body under the entry's barrier
      frame. -/
      def $contId : Machine.Config :=
        .exec ($funcId).body $envT (.frame [] [] [] [] .stop)))
    -- 4. Result locations, in declaration order.
    let mut locItems : Array Term := #[]
    for j in List.range layout.results.length do
      locItems := locItems.push (← quoteLoc (p + j))
    let locsT ← `(([$locItems,*] : List Loc))
    -- 5. The #eval-before-decide guard: both sides of the derived
    --    equation, evaluated at args = 1 / fuel = 100000 / ch = [].
    --    Refuse to emit a theorem whose rfl the kernel would grind on.
    let probeArgs ← kinds.mapM (fun k => `(GoValue.int 1 $k))
    let probeNorm ← kinds.mapM (fun k => `(IntKind.normalize $k 1))
    -- 5a. FIRST: the probe run must actually COMPLETE (pre-merge audit
    --     finding, 2026-08-15). The comparison below is an equality of
    --     two `Except GoError Result` values, so two runs that both end
    --     in `.error .fuelOut` — or both stick the same way — compare
    --     EQUAL and the guard passes on a run that never happened. The
    --     `.ok` assertion on the machine-entry side removes that
    --     vacuous pass: what is compared is a real completed run.
    let probeOkStx ← `(
      match (runFunctionWithContextM 100000 ($progId).typeDefs.toList
          ($progId).funcs $funcId #[$probeArgs,*] ($progId).methods []) with
      | .ok _ => true
      | .error _ => false)
    unless (← liftTermElabM (evalBool probeOkStx)) do
      throwError "derive_entry_eq: the probe run (all args = 1, fuel = \
        100000) did NOT complete — it returned an error (fuel exhaustion, \
        a panic, or a stuck state). An equality of both sides would then \
        be vacuous, so the macro refuses to emit rather than certify the \
        entry equation on a run that never happened."
    let probeStx ← `(
      reprStr (runFunctionWithContextM 100000 ($progId).typeDefs.toList
          ($progId).funcs $funcId #[$probeArgs,*] ($progId).methods [])
        == reprStr ((do
            let r ← runConfig 100000 ($stateId $probeNorm*) $contId []
            return { values := (← loadMany r.1 $locsT).toArray }) :
          Except GoError Result))
    unless (← liftTermElabM (evalBool probeStx)) do
      throwError "derive_entry_eq: the derived entry equation is \
        FALSE at the probe point (all args = 1, fuel = 100000) — \
        refusing to emit an unprovable rfl goal. The derived layout \
        does not match the interpreter's prelude for this Func."
    -- 6. The entry equation itself.
    let argVals ← binders.zipIdx.mapM
      (fun (b, i) => `(GoValue.int $b $(kinds[i]!)))
    let normArgs ← binders.zipIdx.mapM
      (fun (b, i) => `(IntKind.normalize $(kinds[i]!) $b))
    elabCommand (← `(command|
      /-- **The entry equation** (derived by `derive_entry_eq`; §11
      glue): the machine entry IS its post-prelude `runConfig` form —
      the prelude is fuel-independent and definitional at the concrete
      `Func` shape, the parameters land once-normalized, and the
      readback is the result cells in declaration order. Proved by
      `with_unfolding_all rfl` at fully symbolic arguments, fuel, and
      choice stream. -/
      theorem $thmId ($binderF* : Int) (fuel : Nat) (ch : Choices) :
          runFunctionWithContextM fuel ($progId).typeDefs.toList
              ($progId).funcs $funcId #[$argVals,*]
              ($progId).methods ch
            = (do
                let r ← runConfig fuel ($stateId $normArgs*) $contId ch
                return { values :=
                  (← loadMany r.1 $locsT).toArray }) := by
        with_unfolding_all rfl))
  | _ => throwUnsupportedSyntax

end GoLean.Surface.EntryEq
