# Interim pre-merge audit response — the interfaces campaign (2026-07-31)

Branch `quorum-pilot`. The interim adversarial audit of the interfaces
campaign returned **13 CONFIRMED findings**, every one reproduced end to end
against real Go (go1.26.5) through the actual pipeline. This note records
what was changed, what was DELIBERATELY left red, and the decisions taken
where the audit's verifiers and the fix sketch disagreed. Guardrail
discipline was followed throughout: **40 corpus cases were added and
confirmed RED (31) or green-in-the-correct-direction (9) BEFORE any fix**.

Full-run result: **846 cases, 581 PASS / 265 FAIL.** Drift vs the previous
baseline is exactly the 40 new ids plus one recorded improvement flip; ZERO
PASS→FAIL on pre-existing ids.

## The root defect and its fix: wire-level interface declarations

Findings 0 and 2 share one root cause. Interface-satisfaction requirements
were derived by folding the **DISPATCH table** (`state.methods`), which the
frontend populated for non-package-declared interfaces only from methods
actually **CALLED**. With no call site the requirement list was `#[]` and
`Array.all` succeeded vacuously, so `_, ok := x.(error)` was
unconditionally TRUE unless some unrelated line in the package happened to
call `.Error()`. `MethodInfo` also carries no signature, so satisfaction
matched on NAME alone.

Decision: **the interface's method set becomes a wire-level declaration**,
not a projection of the dispatch table.

- `TypeDef.interfaceDef (methods : Array MethodSig)` (`Syntax.lean`);
  `MethodSig` = name + params + results as `Ty` lists, receiver excluded.
- The frontend records EVERY interface type reaching the wire at the single
  type choke point (`emitType`) plus the declaration loop and the
  interface-dispatch call site, then emits one `interface` TypeDef per name
  at the end of `emitProgram`, to a FIXPOINT (a method signature can mention
  a fresh interface). `*types.Interface.NumMethods` is the FULL set, so
  embedded interfaces are already flattened.
- Requirements now come from the declaration; an interface name with **no**
  declaration FAILS CLOSED (`unsupported`). Dispatch anchors are unchanged —
  they remain the executable dispatch table.
- Satisfaction compares canonicalized signatures against the concrete
  method's `Func` (args minus receiver, results).

**The canonical empty interface (`any`) is excluded by design** and carries
no declaration: it is satisfied by every type (Go's `any`). This is both
semantically right and the reason the `recover-direct` and `inc-via-call`
golden lowerings are byte-identical after this change. The legacy key
`empty_interface` (hand-written GoCore terms in `Tests/` and the proof
layer) is recognized alongside `any`.

Known gap, recorded not hidden: `MethodSig` does not carry variadic-ness,
because a `Func` has no variadic flag to compare against — `M(xs ...int)`
and `M(xs []int)` are indistinguishable to the check. Documented on the
structure.

**CLOSED 2026-07-31 by the FINAL pre-merge audit's response (finding 0).**
The gap was a live silent wrong answer, not a theoretical one: the
comma-ok assert returned `true` where Go returns `false`, and the
panicking form ran an ill-typed dispatch where Go aborts with `missing
method M`. Both directions. `Func` and `MethodSig` now carry a `variadic`
flag, the frontend emits `sig.Variadic()` for concrete functions,
methods, lifted literals and interface method-set entries alike, the
decoder REQUIRES the field (a wire without it fails closed rather than
defaulting), and `satisfiesMethodSig` compares it. Guardrails:
`Corpus/coverage/exec/interfaces/method-set-variadic-mismatch` — both
mismatch directions, the panicking form, the positive variadic/variadic
pair, and a variadic pair whose ELEMENT types differ.

## Fail-closures that replace silent wrong answers (deliberate red pins)

Three findings have no correct answer available today. Each is now an
honest `unsupported` with a `docs/BUGS.md` entry and a red corpus pin,
rather than the wrong answer it used to produce.

1. **Method promotion on the ASSERT path (BUG-007, finding 5).** BUG-007
   claimed the promotion gap was "fail-closed — never a wrong answer". That
   was FALSE: all eight pinned cases were dispatch shapes, and on
   `_, ok := any(Outer{…}).(I)` the missing table entry made the answer a
   silently wrong `false`. Detecting promotion soundly is the real fix, so
   the check now fails closed whenever it would answer "unsatisfied" on a
   struct or pointer-to-struct with **embedded fields**. Deliberately
   over-approximate: it fires on any embedded field, whether or not
   promotion would actually apply. The embedded flag is carried on the WIRE
   (`FieldDef.embedded`, from Go's `Field(i).Anonymous()`) rather than
   inferred from field names — name-based inference would put a frontend
   heuristic in the semantic core.
   Pin: `interfaces/promoted-method-assert-ok` (RED).

2. **`preprintpanics` payload rewrite (BUG-004 item 4, finding 3).** The
   campaign replaced a fail-closed `none` with an unconditional
   `main.T(v)`, ignoring that Go rewrites a panic payload to `v.Error()` /
   `v.String()` before printing. Rendering the rewritten form means CALLING
   a method at abort time, which the terminal rule cannot do, so the machine
   returns `none` when the payload's dynamic type has `Error() string` or
   `String() string`. **Deviation from the fix sketch:** the check is made
   against the METHOD SET directly, not by looking up `error`/`fmt.Stringer`
   interface declarations. Those two interfaces are built into the runtime
   and the rewrite applies whether or not the program ever mentions them —
   and the motivating corpus case declares `Error()` without ever naming
   `error`, so a declaration-based check would have failed open on exactly
   the case that found the bug.
   Pins: `panic-defined-payload-methods/{error,stringer}` (RED),
   `/plain` (GREEN — the arm that is correct).

3. **Unknown comparability of imported named types (BUG-008, finding 11).**
   `tyUncomparable` is now three-valued (`none` = UNKNOWN) and the map-key
   hash precheck fails closed on `none`. **Deviation from the verifier's
   suggestion:** the fail-closure is at the USE sites, not at
   `canonicalDynamicTy` (refusing to mint a box tag would have been far
   broader than the defect and risked flipping green cases).
   Pin: `maps/imported-named-key-unhashable` (RED).

## Value-directed map-key hashing, and the two phrasings

Findings 1, 6 and one gap found while probing.

- Go's `typehash` is **value-directed**: it recurses into struct fields and
  array elements, and the panic names the **INNER** type. The precheck is
  now a structural walk over the key VALUE (`valueHashability`), stopping at
  the first offender in Go's own order (fields in declaration order,
  elements in index order). It also recurses INTO a box whose dynamic type
  is statically comparable — the case the type-directed check could never
  see.
- The two phrasings are keyed on the map's **live entry count**, not on
  insert-vs-access (probed 2026-07-31, `.tmp/fix/probe/hash`, 18 shapes):
  `mapassign` never short-circuits and always takes
  `runtime error: hash of unhashable type X`; `mapaccess`/`mapdelete` take
  the `mapKeyError` shortcut (`hash of unhashable type: X`) only while
  `h == nil || h.count == 0`. A map emptied by `delete` returns to the colon
  form. Implemented as `isInsert || !entries.isEmpty`, which leaves every
  `mapEntryIndex?` call site unchanged.
- **Found while probing, not in the audit:** a NIL map still HASHES its key
  — Go panics on `m[k]` and `delete(m, k)` for nil `m` with an unhashable
  `k`, while the machine returned the zero value / no-op. The precheck was
  hoisted into a shared `checkKeyHashable` and is now run on the nil-map
  paths too. This turned the already-pinned red
  `maps/delete-nil-interface-key-panic` GREEN — the one non-new-id flip in
  this wave.

## Panic-message fidelity

Go has FOUR assert-panic shapes where the machine had one (probed
2026-07-31, `.tmp/fix/probe/assert`):

| operand / target | Go |
|---|---|
| any, interface target | `interface conversion: main.T is not main.J: missing method N` |
| nil, interface target | `interface conversion: interface is nil, not main.J` |
| any, concrete target | `interface conversion: interface {} is string, not int` |
| named iface, concrete | `interface conversion: main.I is main.T, not *main.T` |

The source's static type is printed **only** for concrete targets. It is
not recoverable from the runtime value, so it is threaded on the wire:
`Expr.typeAssert` gains `source : Option Ty` (default `none`, so existing
GoCore terms elaborate unchanged and keep the empty-interface spelling).
Only the single-result form panics, so only it carries the field. The
missing-method name comes from `firstUnsatisfiedMethod?`, which returns the
first unmet requirement in the interface's own (name-sorted) order — the
order Go's runtime reports.

## Smaller fixes

- **`**T` method set (finding 4).** The `*T`-inherits-`T`'s-value-methods
  fallback now declines a pointer or interface pointee: Go defines the
  method set of `*T` only for a defined non-pointer, non-interface `T`.
  `concreteMethodForDynamic?`'s signature and success path are unchanged.
- **`canonicalTyFuel` (finding 10).** The docstring claimed fuel bounded
  alias chains only; every arm consumes fuel, so it bounds COMBINED depth
  (real horizon ~512 interleaved levels). Docstring corrected AND the
  exhaustion arms now return `.unsupported`, which `canonicalDynamicTy`
  rejects at boxing time — identity must never be decided on a partly
  resolved type.
- **`runtime.Error` sentinel (finding 9).** Its collision-freedom argument
  ("Go identifiers cannot contain `.`") was falsified by package-qualified
  TypeIds: a package named `runtime` declaring `type Error string` produced
  the identical key. The sentinel is now `$runtime.Error` (`runtimeErrorTypeId`)
  — `$` cannot appear in a Go identifier or package name. Not corpus-pinnable
  (the differential's `go run` oracle cannot express a non-main package).
- **Observation-channel qualification (finding 12).** `Ty.dynamicName` now
  renders named types UNQUALIFIED via `TypeId.unqualified`, matching the
  struct `typeName` field beside it and the channel's stated
  `reflect.Type.Name()` contract (`docs/2026-07-30_interfaces-campaign-design.md`
  §179-182 asserted this; the code contradicted it inside a single JSON
  object). Not corpus-pinnable today: no subject returns an interface.

## Coordination: the proof layer

`Program.typeDefs` gains one entry for the quorum golden
(`main.AckedIndexer`), so `baselines/golden/quorum-lowered.repr` is re-pinned
in this change. **`proofs/GoLeanProofs/Specs/GoldenQuorum.lean`'s
`quorumLowered` term needs the matching entry** — link 2 of
`scripts/check-golden` is red until it lands. The other two goldens
(`inc-via-call`, `recover-direct`) are byte-identical, per the `any`
exclusion above.
