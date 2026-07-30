# Interfaces campaign — design note (quorum-pilot phase 1, 2026-07-30)

Status: DRAFT — machine reading + prior-art comparison done; corpus/
frontend inventory landing (survey in progress). Becomes the design of
record when the identity decision below is validated by the first
slice's differential.

## What the machine has today (read 2026-07-30)

- **Value shape**: `GoValue.interface (dynamic : String) (value)`
  (`Value.lean:240`) — the dynamic type is a RENDERED STRING
  (`dynamicTypeName?`, `Ops.lean:270-280`: `.defined id → id.key`,
  `.pointer (.defined id) → "*"++key`, primitives by name).
- **Dispatch**: `dynamicDispatch?` (`Ops.lean:938`) →
  `methodInfoByFuncId?` → match on `MethodInfo` rows; implements-check
  `dynamicImplementsInterface` (`Ops.lean:317`) compares rendered
  strings; method lookup `concreteMethodForDynamic?` likewise.
- **Asserts**: `typeAssertValue` (`Ops.lean:567`) — string compare for
  concrete targets, method-set check for interface targets; the
  one-result (panic) and two-result (`Stmt.typeAssert`) forms both
  exist in the machine (`Machine.lean:107-108, 482, 516`).
- **TypeDef** (`Syntax.lean:34`): `struct | alias | unsupported` —
  there is NO identity-bearing non-struct defined type. `type T int`
  can only lower as `alias` (= BUG-004's root: identity erased).
- The empty interface appears under TWO keys ("any" from the current
  frontend lowering, "empty_interface" in older material) — works only
  because interface typing is shallow; needs one canonical key at the
  boundary.

## Prior art: Perennial `new/golang/defn/interface.v` (97 lines, read 2026-07-30)

- Interface values carry the **structured dynamic type**
  (`interface.mk_ok from v` — `from` is a `go.type`), never a rendered
  name. Equality: nil/nil true; ok/ok compares dynamic TYPES first
  (structural `decide`), then `CheckComparable` + value equality at
  that type; mixed false.
- Type asserts: concrete target = dynamic-type equality; interface
  target = **type-set containment** computed from the type structure +
  method sets (Go 1.18 general-interface form; we need only the
  method-set fragment for the pilot).
- Convert-to-interface: no-op if already an interface; untyped nil →
  interface.nil; else box with the SOURCE type.
- Dispatch: `MethodResolve` on the carried dynamic type; nil interface
  panics.

**Adopt**: identity is the structured type — matches CLAUDE.md's
"semantic identity is `TypeId`/`FuncId`, never raw frontend strings".
**Adopt**: nil-interface as its own case (GoCore already uses
`GoValue.nil`, kept). **Reject for now**: full type-set/general
interfaces (union terms) — method-set interfaces only; anything else
fails closed at the boundary.

## The identity decision (the campaign's core surgery)

1. `GoValue.interface` carries `dynamic : Ty` (not `String`). The
   dynamic type of a box is a canonical `Ty`: `.defined id`,
   `.pointer (.defined id)`, or a primitive; `Ty` has `BEq` — equality,
   asserts, and dispatch key on it.
2. `TypeDef` gains `| defined (underlying : Ty)` — an identity-BEARING
   named type whose underlying is any non-struct type. `type T int` →
   `.defined` (identity kept, BUG-004 fixed); `type T = int` →
   `.alias` (identity erased, correctly). `Ty.defined id` resolution
   distinguishes the two. Method receivers attach to `.defined` (and
   struct) names only, per Go.
3. `MethodInfo` keys methods by receiver `TypeId` + method name;
   dispatch resolves interface-method calls via the box's dynamic `Ty`
   → method-set lookup. Rendered strings survive ONLY in panic
   messages (`goTypeNameForMessage`).
4. The empty interface canonicalizes to ONE `TypeId` at the NativeToIR
   boundary (collision-checked, per the mangling rule).

Granularity note (for the ledger): dispatch resolution + frame entry
stay ONE step (`enterFrame` already covers it); no new multi-cell
steps are introduced by the identity change — heap untouched, the tag
is control-plane data.

## Slices (each: guardrail cases first, then the change, then the
focused differential + full baseline diff)

- **S1 — guardrail seeding**: edge cases for typed-nil boxes,
  interface equality (same/different dynamic type, incomparable
  dynamic type panic), one- and two-result asserts, type switches,
  value-vs-pointer receivers, defined-type identity
  (`type A int; type B int` — A-box does not assert to B), method
  values through interfaces. Cases classify visibly (blocked, never
  false-pass) before any machine change.
- **S2 — TypeDef.defined + identity plumbing** (BUG-004 fix): syntax,
  resolution (`resolveDefinedAliases` keeps resolving THROUGH alias,
  stops at defined-as-identity for identity purposes while still
  exposing underlying for operations), NativeToIR emission of
  defined-vs-alias, zero-value/normalize/convert paths.
- **S3 — interface value re-keying**: `dynamic : Ty` in the box;
  equality/assert/dispatch/`Describe`-style rendering updated;
  expected transient reds recorded per practice.
- **S4 — frontend emission**: interface decls, method decls (both
  receiver kinds), interface method calls, asserts (both arities),
  type switches (lowering to assert chains — check what the machine
  needs), toInterface at use sites.
- **S5 — the quorum shapes specifically**: methods on defined MAP
  types (`MajorityConfig`), `Index` defined-uint64 arithmetic and
  conversions, `(Index, bool)` two-result interface-method returns.

## Open questions (to resolve during S1-S2, recorded here)

- Q1: does `resolveDefinedAliases`' current fuel/semantics distinguish
  "resolve for operations" vs "resolve for identity"? Needs a split
  (`underlyingTy` vs identity-preserving view) — Perennial's
  `underlying` vs `t` distinction is exactly this.
- Q2 RESOLVED (go probe 2026-07-30): comparing boxes with an
  incomparable dynamic type panics `runtime error: comparing
  uncomparable type func()` — S1 pins it (recoverable, message-exact).
- Q3 RESOLVED (go probe 2026-07-30): a VALUE box does not satisfy a
  pointer-receiver interface; a POINTER box does — the method-set
  check must distinguish receiver kinds. Also probed: typed-nil
  pointer box `!= nil`; `type A int`/`type B int` boxes assert only to
  their own identity (the BUG-004 guardrail pair); dispatch through an
  interface on a defined-int receiver returns the concrete method's
  value.

## Survey inventory (returned 2026-07-30)

107 interface-blocked FAILs: 100 frontend-export (86 = the implicit-
conversion guard alone — the single unlock; 3 type switches, 4 method
expressions, 2 type asserts, 2 typeparams, 2 chans, 1 anonymous
non-empty interface, plus generics-lane overlap), 7 lean-observation
(promoted/embedded-method receiver mismatch ×2, receiver auto-deref ×1,
nil-value-receiver ×1, map interface-key delete panics ×2, interface-
slice-key conversion ×1). Frontend had NO emission for asserts, type
switches, dispatch, or method values; NO defined-vs-alias wire
distinction. Decoder had Ty.interface, the MethodInfo table, and
toInterface (panic-wrap only). Corpus seed: 54 interface + 22 method
cases incl. `acked-indexer` (the AckedIndexer reduction) and
`interface-defined-type-identity` (the BUG-004 discriminator) — S1
needed no new cases beyond the two probes already recorded.

## Implementation record (S2+S3 landed 2026-07-30, this branch)

- `TypeDef.defined (underlying : Ty)` (S2): frontend emits kind
  "defined" for `type T <non-struct>` (true aliases never reach the
  wire — go/types materializes them as *types.Alias, filtered by the
  *types.Named check); machine threads normalize/default/convert/
  valueEq through the underlying; `resolveDefinedAliases` stops at
  defined (identity view). Focused differential: the three defined-type
  method PASSes hold.
- `GoValue.interface (dynamic : Ty)` (S3 — the string tag DID have to
  go): box-vs-box equality needs the payloads compared AT the dynamic
  type, which a rendered string cannot recover. `Ty` moved to
  Value.lean (same precedent as FuncId), staying in the `GoCore`
  namespace (repr pins). `canonicalTy` (deep alias resolution, defined
  stops) defines dynamic-type identity; `canonicalDynamicTy` fails
  closed on unsupported leaves at box time. Equality: different
  canonical dynTy → false; same → `tyUncomparable` check (resolved
  through defined; struct fields/array elems recurse) panics
  `comparing uncomparable type <name>`, else valueEq at the dynamic
  type. Asserts: concrete = canonical BEq (slice/map/array dynamics now
  assertable); interface = method-set check.
- Method sets (Q3): `concreteMethodForDynamic?` returns (method,
  needsDeref) — direct receiver match first, else pointer-box →
  value-receiver method with auto-deref at dispatch (nil pointer →
  Go's nil-deref panic). Value box never satisfies pointer-receiver.
- Dispatch protocol: interface methods ride the wire as body-less
  method entries (`"interface": true`); the decoder synthesizes a
  signature-only anchor Func ("I.M") whose stub body is a call to a
  nonexistent function (STUCK if a dispatch bug ever reaches it —
  never a silent zero return); `dynamicDispatch?` intercepts at
  enterFrame on the receiver box, and throws Go's nil-deref panic on a
  nil-interface receiver.
- Wire contract added: expr "to-interface" {target, dynamic, operand};
  expr "type-assert" {operand, target}; stmt "type-assert" {target,
  okTarget, expr, targetType} (blanks → typed discard temps).
- Proof impact of S3: exactly two payload literals + two happly
  discharges (simp with the canonicalization defs) — both composition
  walks and the full Audit sweep (5157 decls) green same-session.
- First full differential after the wrap/dispatch/asserts landed:
  **787 = 512/275 (+41 net, ZERO PASS→FAIL)**; 15 formerly
  frontend-blocked cases now die VISIBLY at machine gaps
  (lean-observation) and 2 at message fidelity — all triaged same-day:
  - message fidelity (both fixed): funcType signature rendering
    (`func()` not `func`); package-qualified TypeId keys (frontend
    emits `main.X`; the observation channel strips the qualifier the
    way `reflect.Type.Name()` does; identity stays qualified — the
    phase-2 cross-package requirement landed early).
  - machine gaps (fixed): convert-INTO-interface identity for
    boxes/nil (raw values fail closed — a raw value reaching an
    interface conversion is a lowering bug by construction);
    unhashable-key precheck at `mapEntryIndex?` (Go hashes before
    comparing: `hash of unhashable type []int` even on empty maps);
    defined-type abort rendering `main.Code(7)` (BUG-004 item 2).
  - frontend gaps (second agent slice): map-index READ keys +
    `delete` keys wrap; synthesized anchors for predeclared/imported
    interfaces (`error.Error`).
- **Owed sub-slices, recorded not dropped** (all visibly red, none on
  the quorum path): method PROMOTION through embedded fields (7 cases
  incl. the pre-existing embedding backlog); interface method
  VALUES/EXPRESSIONS (4); type SWITCHES (the 15-dir corpus family);
  anonymous non-empty interfaces (1); multi-value-assign tuple wraps
  (2, deferred refusals at the frontend); interface-valued OBSERVATION
  positions (harness renders concrete values only — no corpus case
  observes a box yet; decide the channel shape when one does).
