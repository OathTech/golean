# Embedding, promotion, type switches, assignability — design note (general-coverage slice 2)

Scope (arc plan slice 2): BUG-007 (method/field promotion through embedded
fields), type switches, BUG-011 (`struct{}{}` assignability), BUG-009's
satisfaction polarity for the `assert-imported-method-set` cluster, and the
riders these unlock. Target reds, grounded in `baselines/native-full.tsv`
(recorded 2026-08-04, 636/888) — each case's canonical Go and recorded
failure read before deciding:

- **Promotion (BUG-007), stuck/unsupported at the machine:**
  `embedding/{deep-promoted-field, deep-promoted-method,
  embedded-method-promote, embedded-pointer-field,
  embedded-pointer-nil-panic, promoted-field-depth-shadow}`,
  `structs/anonymous-field`, `structs/tag-embedded-field`,
  `methods/embedded-interface-satisfaction`,
  `interfaces/embedded-interface-shadowing/{interface-field-dispatch,
  interface-field-nil-panic, nil-pointer-method-promoted,
  pointer-method-promoted}`, `interfaces/error-idioms/promoted-method`,
  `interfaces/promoted-method-assert-ok`. Failure shapes: promoted field
  reads/writes hit `unknown GoCore struct field`, promoted method calls
  pass the OUTER value where the method expects the embedded receiver
  (`struct value type mismatch`), satisfaction on embedded-field types is
  the deliberate BUG-007 fail-closure.
- **Type switches, frontend-quarantined `*ast.TypeSwitchStmt`:** the 14
  `interfaces/type-switch-*` ids plus `scoping/type-switch-guard-shadow`;
  `methods/nil-receiver-interface-dispatch` rides (anonymous non-empty
  interface type in a case/assert position).
- **BUG-011:** no corpus case yet (owed from the sem-adequacy arc) —
  `structs/empty-struct-literal-at-named-type` is added FIRST, then the
  fix.
- **Imported method sets (BUG-009 polarity):**
  `interfaces/assert-imported-method-set/{comma-ok, panic-form}` — the
  machine's deliberate fail-closure because `*strings.Builder`'s method
  set is not on the wire.
- **Riders:** `interfaces/{interface-method-value,
  interface-method-expression}` + `defer/defer-interface-value-eval`
  (interface method values), `functions/composite-function-values/*`
  (calls through func-typed struct fields),
  `structs/tag-defined-conversion` +
  `structs/selector-addressability-edge/read-conversion-result` (value
  conversions between structurally identical struct types).

Ground truth surveyed before deciding: the machine's method-set/dispatch
layer (`GoLean/GoCore/Ops.lean`: `concreteMethodForDynamic?`,
`satisfiesMethodSig`, `firstUnsatisfiedMethod?`, `dynamicDispatch?`,
`typeAssertValue`, `normalizeStructValueWith`, `convertValueToTyFuel`),
the frontend (`tools/nativefrontend/emit.go`: `emitSelector`,
`emitAddressOf`, `emitMethodCall`, `emitSwitch`, `emitProgram`'s method
table; `wire.go`: `emitType`), the decoder (`GoLean/NativeToIR.lean`:
`decodeMethod`, `decodeFunc` stubs, `decodeTypeDef`), the Go spec's rules
(promotion depth/shadowing/ambiguity, method sets of `T` vs `*T`, type
switch, assignability §Assignability, conversions §Conversions), and
Goose (`deps/goose/goose.go`).

**Goose comparison.** Goose has a `typeSwitchStmt` (goose.go:1910) that
compiles a type switch to sequential `interface.tryGet`-style tests —
the same first-match if-chain shape chosen below. For embedding, Goose
handles single-embedded-struct field lookup (goose.go:788, one embedded
field, struct only) and has no general promotion, no wrapper synthesis,
no promoted method-set satisfaction; Perennial's interface support is
similarly narrow. Everything in the promotion stage exceeds Goose's
coverage, so the design is against the Go spec with `go/types` as the
static oracle, mirroring how gc itself compiles promotion.

## D1 — promotion is resolved in the FRONTEND (flattening + wrappers), not by a machine method-set walk

Two honest options:

(b) **machine-level walk**: satisfaction/dispatch recursively search
embedded fields (the `FieldDef.embedded` flag is already on the wire).
Rejected: it re-implements go/types' subtle rules (depth-first
shallowest-wins shadowing, same-depth ambiguity exclusion, the `T` vs
`*T` method-set asymmetry through value/pointer embedding) as a SECOND
implementation in Lean — with cycles to fuel (Go permits
`type T struct{ *T }`), receiver-adjustment through field paths as new
step semantics (today dispatch adjusts a receiver by at most one deref),
hence new Step rules + stepFn arms + correspondence proofs. High cost,
and the machine would still trust the frontend for everything else
name-shaped.

(a) **frontend flattening**, chosen (and already the recorded fix
direction in BUG-007's entry): the frontend resolves every promoted
access at emission using `go/types`' `Selections` (the `Index()` path
through embedded fields), and synthesizes FORWARDING WRAPPER methods for
the promoted method set so the machine's flat `TypeId`/`FuncId` method
table is COMPLETE. This mirrors gc (promoted static calls are compiled
with inlined field adjustment; itab entries get compiler-synthesized
wrappers). GoCore stays pure and flat; no new step semantics; semantic
identity stays `TypeId`/`FuncId`.

Mechanics:

1. **Field promotion** (`o.x` with selection index length > 1): reads
   walk the hop chain as `field-get` nodes (auto-deref at embedded
   POINTER fields — a nil embedded pointer panics at the deref, Go's
   panic); writes/addresses walk `field-addr` chains from the
   addressable root, taking the pointer field's VALUE at embedded
   pointer hops. Both are the existing single-hop lowerings iterated;
   no new wire nodes.
2. **Promoted method calls and method values**: the receiver argument is
   adjusted AT THE CALL/VALUE SITE through the hop chain (value hops:
   `field-get`; final receiver: value, deref, or `field-addr` per the
   receiver kind vs reaching-field kind), and the call targets the
   ORIGINAL method's FuncId. Call-site adjustment, not a wrapper call,
   because a method VALUE captures the ADJUSTED receiver at
   value-creation time (a wrapper would re-walk the path at call time —
   observably different when an embedded pointer field is reassigned
   between the two; `promoted-method-value/{snapshot,live}`). Panic
   timing vs argument effects (corrected per audit F3, 2026-08-05: an
   earlier draft claimed gc panics the receiver's auto-deref BEFORE
   argument effects — FALSE; probed, gc runs an argument-position call
   first, `calls = 1`): the lowering agrees with gc because ANF hoists
   argument calls ahead of the whole call statement, so they run before
   the receiver walk's deref either way —
   `promoted-nil-embedded-pointer/before-args` pins the agreement, not a
   receiver-first order.
3. **Wrappers for dynamic dispatch**: for every named struct type
   declared in the package (package-level and function-local) the
   frontend computes `types.NewMethodSet(T)` and `NewMethodSet(*T)`;
   every entry with a multi-hop index gets a synthesized wire method —
   receiver `T` when the entry is in `T`'s method set, else `*T` — whose
   body walks the hop chain from `$recv` and calls the original method
   (or, for a method promoted from an embedded INTERFACE field,
   dispatches `Iface.M` on the field value — a nil field then panics at
   dispatch, Go's nil-interface-call panic). Wrapper emission failure
   fails the whole export, the existing policy for methods — so a
   method table that IS on the wire is complete, which is what the
   machine's satisfaction logic relies on (D2).
   ADDENDUM (arc-final audit F1 / BUG-015, 2026-08-06): this note never
   considered the wrapper frame's consequence for the RECOVER WALK. gc
   marks the same synthesized wrappers `abi.FuncIDWrapper` and its
   gorecover skips them ("there must be exactly one non-wrapper frame
   between gopanic and gorecover", runtime/panic.go) — an unmarked
   wrapper frame made `recover()` inside a promoted method return nil
   (silent value divergence + status flip; the audit's decisive
   finding). DECLARED SCHEMA ADDITION: synthesized wrappers carry
   `"wrapper": true` on the wire (only `synthesizeWrapper` emits it);
   `Func.wrapper` (Syntax.lean, default false) threads it into the
   frame continuation (`Cont.frame`'s trailing marker), and
   `recoverResult` — and ONLY the recover walk; chain joining, defer
   draining, and panic status treat wrapper frames as ordinary — skips
   wrapper frames (`recoverThroughWrappers`). Pinned by
   `interfaces/recover-promoted-wrapper/*`: all three wrapper paths
   plus four agreeing controls.
4. **Embedded-interface dispatch at static call sites**
   (`emitMethodCall`'s deferred branch): the receiver expression walks
   to the interface FIELD value, then dispatches `Iface.M` — same shape
   as the wrapper body.

## D2 — the BUG-007 satisfaction fail-closure is REMOVED; the wire contract changes

`firstUnsatisfiedMethod?`'s `dynamicHasEmbeddedFields` guard exists
because the method table used to lack promoted entries, making a
definite "unsatisfied" unsound. Under D1 the wire contract is: **the
emitted method table carries the FULL method set of every declared named
type, promoted methods included (as wrappers)** — the same completeness
contract `dynamicMethodSetRecorded` already documents for declared
methods. With the contract extended, a missing method on an
embedded-field type is real information and the guard is a dead
over-approximation; it is removed in the same commit that lands wrapper
synthesis. Hand-written GoCore terms (Tests/, proofs) are now subject to
the same contract: a term-author who wants promotion must supply the
flattened entries, exactly as they already must supply declared methods.
Satisfaction stays fail-closed for what is genuinely unknown (imported
types without declarations — BUG-009's `dynamicMethodSetRecorded`
guard is untouched by this slice's promotion work; see D5).

Negative-polarity pins added with the removal (the guard's honest job,
now answerable): same-depth ambiguity (method set has NO such method —
comma-ok `false`, Go agrees), and a pointer-receiver method promoted
through value embedding (in `*T`'s set only: value box fails the
assert, pointer box passes).

## D3 — type switches: frontend desugar onto comma-ok asserts (first-match if-chain)

`switch [init;] v := x.(type) { ... }` lowers in the frontend (no new
machine machinery; `Stmt.breakable` + the comma-ok `type-assert`
statement + `==` on interfaces already exist):

```
breakable block {
  init
  $tsN := x                       // guard evaluated ONCE (hoists legal)
  case nil        → $mK := ($tsN == nil)
  case T          → $vK, $mK := $tsN.(T)      // comma-ok, no panic
  case T1,...,Tk  → $mKi per type; $mK := $mK1 || ... (no binding value)
  if-chain in SOURCE order (default last in position, else-branch):
    clause body as a sibling block, prefixed by the binding:
      single-type clause:  v := $vK   (v : T)
      nil/multi/default:   v := $tsN  (v : guard's static type)
}
```

- First-match textual order = the if-chain; case tests are effect-free
  (comma-ok asserts cannot panic), so eager per-case test evaluation is
  observationally silent, and only the ORDER of first match is
  load-bearing (`type-switch-first-match`).
- `case nil` matches exactly the nil interface; a typed nil box does not
  (`type-switch-typed-nil*` pins; the machine's boxed-nil comparison
  semantics is already differentially green).
- Bindings come from `go/types`' `Implicits` per clause; the desugar
  declares `v` at clause-block top, so guard shadowing
  (`scoping/type-switch-guard-shadow`: `switch v := v.(type)`) resolves
  in the outer scope for the guard and the clause scope for uses — Go's
  rule.
- No fallthrough exists in type switches (spec), so no `$swf` machinery.
- Labeled type switches: `emitLabeled` accepts `*ast.TypeSwitchStmt`
  exactly like `*ast.SwitchStmt` (label onto the `breakable`).
- **Anonymous non-empty interface types** (a `case interface{ M() }`,
  assert targets, variable types) get canonical wire names via
  `types.TypeString` — sound because Go interface identity IS structural,
  so structurally identical spellings are one type. They register in
  `seenInterfaces` and get full `interface` TypeDefs like named ones.
  (This also un-reds `methods/nil-receiver-interface-dispatch`.)

## D4 — BUG-011: assignability-aware normalization at the machine's empty-struct boundary (corpus case first)

The wire has exactly ONE unnamed struct type: the canonical `struct{}`
(`emptyStructName`; all other anonymous structs fail closed at
`emitType`). Go's assignability rule (identical underlying types, at
least one side not a defined type) therefore reaches the machine in
exactly one shape: a `struct{}`-tagged value at a defined
empty-underlying type, or the reverse. Decision: fix in
`normalizeStructValueWith` (Ops.lean) — the mismatch branch retags when
one side is the canonical unnamed `struct{}` and both field lists are
empty (empty fields ⟺ identical underlying here). Normalization sites
are precisely Go's assignment contexts (declared-type stores, param
binding, composite fields, map/append elements), so the retag encodes
assignability, not identity: two DIFFERENT defined types still mismatch
(`stuck`), as Go requires. The frontend-retag alternative would thread
assignment-context types through every emission site
(`wrapInterfaceConversion`-style) to fix what is one machine-side
branch; rejected as more surface for the same behavior. The corpus case
(`structs/empty-struct-literal-at-named-type`, multiple subjects: var
init, param pass, return, map-element store, mixed `==`) lands and
classifies red BEFORE the fix commit, per the standing rule and the
BUGS.md entry's explicit owed-case note.

## D5 — imported named types: method-set stubs (the BUG-009 satisfaction polarity)

`*strings.Builder` implements `fmt.Stringer`; the machine correctly
refuses to answer because the imported type carries no declaration. Fix
within this slice's scope (satisfaction/assert polarity only, not
executing imported methods):

- The frontend records every IMPORTED named non-interface type whose
  identity reaches the wire; for each, if EVERY method signature in
  `NewMethodSet(T) ∪ NewMethodSet(*T)` is emittable, it emits (1) an
  `unsupported`-kind TypeDef (`imported named type <T>` — any structural
  use keeps failing closed, only the type's EXISTENCE is recorded) and
  (2) one signature-carrying METHOD STUB per method-set entry.
- If any signature fails to emit, NOTHING is emitted for that type — the
  machine's `dynamicMethodSetRecorded` guard then fails closed exactly
  as today. Monotone: strictly more definite answers, never a new wrong
  one.
- **ADDENDUM (2026-08-10, BUG-053 class closure —
  `docs/2026-08-10_method-set-record-contract.md`):** the guard behind
  this design was re-keyed. As written here, `dynamicMethodSetRecorded`
  keyed on the TYPE-KIND taxonomy — `.defined` consulted TypeDef
  presence, every other kind got a blanket "can carry no methods"
  `true`. That blanket arm was the latent hole: it was a claim about
  the kinds that EXISTED in 2026-08-05, silently inherited by any later
  kind modeling a method-carrying Go type — which is exactly how
  `Ty.sync` answered wrong "no"s (BUG-053). The guard now keys on
  RECORD PRESENCE: the wire carries an explicit `methodSets` entry
  (`full`/`exported` coverage) for every method-carrying type, the
  skip-whole posture above leaves no record (same refusals as before,
  now by the general rule), and the marker-TypeDef sniffing that
  implemented the unexported-requirement refusal
  (`dynamicIsImportedMarker`) became coverage `exported`
  (`dynamicMethodSetExportedOnly`). The taxonomy survives only as the
  carrier/non-carrier split, whose non-carrier half is a gc-probed
  language fact (type literals cannot carry methods), not a
  registration default.
- `NativeToIR.decodeMethod` accepts the stub form (full recv/params/
  results + an `unsupported` reason instead of a body): it registers the
  `MethodInfo` and a `Func` whose body is `Stmt.unsupported`, so
  `satisfiesMethodSig` compares real signatures while CALLING the method
  stays a visible refusal.
- Promotion inside imported types needs no wrappers here: the method-set
  stubs are generated from `types.NewMethodSet`, which already contains
  promoted entries, and they exist only to answer satisfaction — a
  wrapper BODY would be dead weight behind an uncallable stub.

## D6 — riders taken and not taken

Taken (each with the failing case(s) as guardrails, plus edges):

- **Interface method values** (`x.M` with `x` an interface):
  `func-value { func: "Iface.M", captured: [x] }` — the dispatch anchor
  is already a real `Func`, and `enterFrame`/`dynamicDispatch?` resolve
  through it on the call; the box is captured at value time
  (`defer/defer-interface-value-eval`'s pin). A NIL interface panics at
  CREATION — the itab load — via a hoisted nil check (corrected per the
  build log and audit F6: this bullet originally claimed panic at CALL
  time, which the oracle refuted on `interface-method-value-nil`).
- **Method expressions** (`I.M`, `T.M` in expression position) —
  `interfaces/interface-method-expression`: `T.M` is a func value taking
  the receiver first, which is EXACTLY the GoCore method function;
  `I.M` is the dispatch anchor. Emit `func-value` with no captures.
- **Calls through func-typed struct fields**
  (`functions/composite-function-values/*`): `emitMethodCall` currently
  refuses any selector call whose selection is not a method
  (`FieldVal` of func type). Route it to the ordinary call-through-value
  path (`call-value` with the field read as callee) — this composes with
  promotion (a promoted func field works via the D1 walker).
- **Struct VALUE conversions with identical underlying**
  (`structs/tag-defined-conversion`,
  `structs/selector-addressability-edge/read-conversion-result`):
  `convertValueToTyFuel`'s `.struct` arm retags when the operand's
  resolved struct fields are equal to the target's (wire `FieldDef`
  equality — tags are already absent from the wire, so Go's
  ignore-tags conversion rule is the wire equality; `embedded` flags
  must match, a recorded CONSERVATIVE narrowing vs the spec, which
  ignores embeddedness for identity). A retagged COPY is exactly Go's
  value-conversion semantics.

Not taken, stays red, reasons:

- `structs/tag-pointer-conversion`: `(*B)(pa)` aliases one heap cell
  under two struct tags; GoCore field load/store checks the stored tag,
  so honest support needs identity-up-to-underlying at every
  field-access site — a machine-semantics change of its own (and the
  granularity of "which tag does the cell hold" needs a design pass).
  Fail-closed `unsupported` at the conversion, message names the shape.
- `structs/tag-unnamed-conversion`, `structs/tag-nested-conversion`:
  anonymous NON-EMPTY struct types. A canonical-name scheme must NOT
  collapse types differing only in tags (tags are identity for
  assignability but not for conversion), so the wire needs tags —
  deferred whole, fail-closed at `emitType` as today.
- `interfaces/imported-package-name-collision`: TypeId keys are
  name-qualified, Go keys identity on import PATH — the existing
  deliberate fail-closure; fix is a key-scheme change, not this slice.
- `interfaces/error-idioms/extra-interface-assertion`: red on `call in
  short-circuit operand` (`ok && x.Temporary()`) — general lazy-operand
  restructuring, control-flow class, not interface machinery.
- `interfaces/typed-nil-channel`: channel-blocked (its own arc).
- `defer/defer-interface-value-eval` additionally needs named-result
  machinery review — taken only if the method-value rider alone turns
  it green; otherwise its residual reason is recorded after the run.
- `embedding/embedded-pointer-nil-panic` note: the read `o.x` through a
  nil embedded pointer panics at the auto-deref — covered by D1(1).

## Stage plan (one semantic concern per commit, gates per stage)

0. This note + guardrail corpus additions (BUG-011 case; promotion
   negative-polarity pins; interface-method-value nil edge; type-switch
   init-statement + labeled-break pins), classified before any fix.
1. BUG-011 normalization fix (Ops.lean) + BUGS.md update.
2. Field promotion (frontend walker: reads, writes, addresses).
3. Method promotion: call-site receiver adjustment, method values,
   embedded-interface static dispatch, wrapper synthesis, D2 guard
   removal (Ops.lean) + BUGS.md BUG-007 update.
4. Type switches + anonymous interface types (+ labeled type switch).
5. Interface method values/expressions + func-field calls.
6. Imported method-set stubs (frontend + NativeToIR) + BUGS.md BUG-009
   update.
7. Struct value conversions (Ops.lean convert arm).

Each stage: focused differential slice + `lake exe gocore-eval-tests`;
full `scripts/ci --diff` with baseline re-pin (dated header, reasons,
zero PASS→FAIL) in the same commit as the movements. Machine-touching
stages (1, 3's guard removal, 7) change only shared `Ops.lean`
value-level functions used identically by the relation and the
interpreter — no Step rules, no stepFn arms, no continuation forms, no
`Choices` sites, so the lockstep obligations are discharged by
construction (no correspondence statement mentions these definitions'
internals); `proofs/` stays untouched (its simp sets unfold
`normalizeStructValueWith` only at concrete `actual == name` instances,
which the changed mismatch branch does not affect — verified by the
proofs build in the gate).

## Build log — deviations and discoveries (recorded as they happened)

- **Stage 1 (BUG-011).** The Ops change rippled into core metatheory as
  predicted-but-underestimated: `normalizeStructValueWith_locSup`
  (StateWf) and MachineSound's capCong-congruence and default-value
  lemmas needed the escape branch — all in the same commit; `proofs/`
  itself needed nothing.
- **Stage 4 (type switches).** Two frontend defects found by the
  differential during the stage, fixed before its re-pin: (a) the
  type-checker config never requested `Implicits`, so clause bindings
  were absent (silent wrong answer on `scoping/type-switch-guard-shadow`:
  outer `v` resolved inside clauses); (b) `freeCaptures` classified
  Implicits-declared clause bindings as OUTER captures — a func literal
  containing `switch r := recover().(type)` captured a nonexistent outer
  `r` (`panic-recover/recover-value` moved stages, then went green).
- **Stage 5 (method values) — the oracle earned its keep twice.**
  (a) Go panics at method-value CREATION on a nil interface (the itab
  load), not at the call: the first lowering captured the nil box and
  panicked at call time — Lean 12 vs Go 2 on the stage-0 pin
  `interfaces/interface-method-value-nil`, whose in-file comment had
  encoded the same wrong assumption (both corrected). The lowering now
  hoists the box once and nil-checks it at creation, panicking with the
  machine's runtime-error payload — new wire form `panic` +
  `runtimeError: true`, decoded as a box at `runtimeErrorTypeId` (the
  sentinel moved Machine.lean → Syntax.lean so the decoder can name it).
  (b) A PRE-EXISTING machine gap surfaced: frame-entry panics
  (`dynamicDispatch?`'s nil-interface and nil-pointer-box-deref panics
  inside `enterFrame`) were raw thrown errors on EVERY call path —
  correct panic status when unrecovered, wrong under `recover`. Pinned
  first (`interfaces/recover-nil-dispatch/{nil-interface,
  nil-pointer-box}`, red), then fixed in LOCKSTEP: five `Step` twins
  (`callImmediatePanic`, `callTargetsDoneEnterPanic`,
  `callArgsDoneEnterPanic`, `callValCalleeEnterPanic`,
  `callValArgsEnterPanic`) appended at the END of the inductive (the
  correspondence proofs' positional case tags keep their numbering) and
  a single `enterFrameStep` helper in stepFn (each call site stays ONE
  `fun_cases` branch); `stepFn_sound` / `step_complete` /
  `step_complete_any_wf` / `stepFn_oblivious` extended,
  `step_preserves_wf` and `step_det` (proofs/, bit-identical) absorbed
  the new rules unchanged. A narrowing was recorded here for
  DEFERRED-call frame entry — **retired by the audit response below
  (F1+F5): its justification (chain-joining semantics) only ever applied
  to the panic-path drain, and all three drain sites are now modeled.**
- **Stage 5 bonus:** the method-expression lowering turned three
  long-red ids green that were not in this slice's target list
  (`methods/method-expression`, `methods/pointer-method-expression`,
  `variadic/variadic-method-expression`).
- **Stage 6 (imported stubs).** The unexported-method identity hazard
  (D5's "cross-package unexported" case) got an explicit machine guard:
  `dynamicIsImportedMarker` + `isExportedName` in
  `firstUnsatisfiedMethod?` — an unexported requirement never gets a
  definite answer against a marker type.
- **Stage 7.** As designed; `structs/tag-pointer-conversion` stays red
  with the aliasing reason recorded in the convert arm's comment.

## Audit response, 2026-08-05 (independent audit of the branch; 8 confirmed findings)

- **F1+F5 (MAJOR): deferred-call frame-entry panics were unrecoverable.**
  The stage-5 fix covered the five ordinary call-entry sites only; the
  three drain sites still threw raw errors — status `panic` on programs
  Go completes, a shape the stage-5 method-value lowering itself
  unlocked. The recorded narrowing's justification applied only to the
  panic-path drain. Fixed in lockstep at all three sites: normal drains
  mirror the `.nil`-callee rules (the entry panic is the deferred
  INVOCATION's panic — unwinds at the draining frame with its remaining
  defers); the panic-path drain JOINS the chain newest-last (mirror of
  `panicFrameDeferNil`; Go appends the new panic and `recover` answers
  the newest entry, which `chainNewestRecovered` implements). Pins
  (fresh canonical Go, red first):
  `defer/deferred-dispatch-entry-panic/{return-drain, fallthrough-drain,
  during-panic}` — the last discriminates newest-vs-original by
  asserting the recovered value.
- **F2 (MAJOR): wrapper synthesis refused a legal method-set shape and
  killed whole exports.** A pointer-receiver method promoted through an
  embedded POINTER hop is in the VALUE method set (spec: embedding `*T`
  contributes both receiver kinds); the wrapper path lacked a
  value-rooted walker and refused, failing the entire package on mere
  declaration (raft-relevant shape). Fixed: `valueRootedFieldAddr`
  (value-walk to the pointer hop, address-walk beyond); the in-code
  method-set claim corrected. Pins:
  `embedding/value-embedded-pointer-promotion/{static-call,
  value-box-satisfies, dynamic-dispatch}`.
- **F3 (MINOR): D1's evaluation-order rationale was false for gc** — an
  argument-position call runs BEFORE the receiver's auto-deref panic
  (probed: `calls = 1`); the lowering agrees with gc through ANF
  hoisting, not receiver-first ordering. D1 item 2 and the
  `promoted-nil-embedded-pointer` case comment corrected; the call-site
  adjustment decision stands on the method-value capture-moment
  argument.
- **F4 (NOTE): the equality-site empty-struct escape fired on the
  CONTEXT key too**, letting two DIFFERENT defined empty types compare
  equal at a `struct{}` context (that wrong-answer path is
  hand-written-terms-only). First tightening (a1e3b5a) required the
  mismatching operand's OWN tag to be canonical — which over-tightened a
  FRONTEND-reachable case: with the anonymous literal as the LEFT
  operand, the context is the unnamed `struct{}` and the DEFINED-typed
  operand is the mismatching one (`struct{}{} == m` went stuck;
  delta-review R1, pinned by
  `structs/empty-struct-literal-left-operand/{eq,neq,switch}`). Final
  guard is PAIR-level: a mismatching operand is admitted iff the operand
  pair is Go-comparable — equal tags, or either side tagged the
  canonical `struct{}`; two DIFFERENT defined types are rejected at
  every context.
- **F6 (NOTE):** the emit.go interface-method-value comment and the D6
  bullet still asserted the falsified panic-at-call claim; both
  corrected (the build log had recorded the discovery, the shipped
  comments had not).
- **F7 (NOTE):** a present-but-malformed `runtimeError` wire flag fell
  open to a user-string panic payload; the decoder now decodes a present
  key strictly.
- **F8 (NOTE, record correction):** commit 5c2f725's baseline header
  says "the ten stage-0 guardrail pins" where eight are enumerated
  (promoted-ambiguous-not-satisfied, promoted-method-value ×2,
  promoted-nil-embedded-pointer ×3,
  promoted-pointer-receiver-method-set ×2); the total of seventeen
  FAIL→PASS is correct (9 BUG-007-list ids + 8 pins). History is not
  rewritten; this line is the correction of record.
- Refuted by verification, no action: the D2 contract-marking,
  anonymous-interface naming, and stage-0 re-pin complaints.
