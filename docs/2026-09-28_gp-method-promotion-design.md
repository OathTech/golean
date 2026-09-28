# G-P — native method promotion: the design note (2026-09-28)

Status: PROPOSED, HARD-STOP gate ([AGENT] writer; `docs/gp-design-0928` off `train/r52` @ `d640a5ac`); nothing implemented; the [USER] passes or
amends §6. Inputs: G-P ruled in principle (`docs/2026-09-04_reasoning-surface-plan.md` §3.P/§5.4; 2026-09-04, confirmed 2026-09-05, [USER] relayed);
window row 3 (`docs/2026-09-23_batched-window-charter.md`, `docs/2026-09-24_window-plan.md`); logic team §4 «P / methods»; proposal §2(b). Spec pin `c19862e5f8`.

## 1. What changes and why

**Today** ([AGENT], read from the code). Promotion is split. The *static* surface is already native in the frontend: a direct call `x.M()`, a method
value `x.M`, and a constraint call on a type parameter (re-resolved by `LookupFieldOrMethod`) lower to a field-projection / deref / address chain over
`Selection.Index()` plus an ordinary call to the DECLARED method (`promotedReceiverArg`, `tools/nativefrontend/emit.go:6392`; call site `:9480`;
method value `:7132`). The *dynamic* surface goes through synthesized forwarding functions: `synthesizePromotionWrappers` (`emit.go:6018`) emits one
`Func` per promoted method-set entry of every named struct (receiver `T` if the entry is in T's set, else `*T`), marked `"wrapper": true` (`:6298`),
so the flat method table is COMPLETE (the D2 contract, `docs/2026-08-10_method-set-record-contract.md` §3). Wrappers are reached by interface dispatch
(`dynamicDispatch?`, `Ops.lean`), interface satisfaction (`satisfiesMethodSig` reads the wrapper's signature), and method expressions `S.M`
(`emit.go:7142`). Promoted sync-primitive methods and FR-23 signatures get declaration-only stubs instead (`syncPromotedStub`, `promotedSigStub`).

**Counts** ([AGENT], measured 2026-09-28 over the 3732 corpus wire files of the r52 step-label lane's trace run,
`.claude/worktrees/step-label/.tmp/ct-lane/wire`, read-only, not regenerated; twin from `baselines/pins/twin-chdriver.wire.json`): corpus **678
wrappers in 182 wires** (75 with a `*T` receiver), plus **62 promoted stubs**. Only **18 wires** name a wrapper statically (method expressions); the
rest are reached only by dispatch/satisfaction (dynamic, not counted). Twin: **53 wrappers** (50 `T`, 3 `*T`: `tracker.ProgressTracker`,
`raft.DefaultLogger` over the imported `*log.Logger` incl. the unexported `log.output`, `raft.{Ready,Status,BasicStatus}` over the pb messages) + **3
promoted stubs**, out of 537 methods.

**Core consumers of `Func.wrapper`** ([AGENT]). There are more than the plan's four. The `Cont.frame … w` marker is set at 6 entry sites in
`Machine.lean`, 6 in `StepFn.lean` and 1 in `Multi.lean` (spawn). The other consumers: `Cont.recoverTransparent` / `recoverThroughWrappers` /
`recoverResult` (BUG-015); `dispatchLeaf` + `wrapperForwardArg` + `recvFieldChain` (race narrowing, which recognizes the wrapper's BODY SHAPE);
`nilValueMethodText?` (BUG-087 family); `ChoiceTrace.nilTextFacts`; `AdmissionPolicy.BooleanSyntax`; `SyntaxEqb`; the decoder;
`StateWf.recoverThroughWrappers_locSup` and the MachineSound arity.

**After P** ([AGENT] proposal). No synthesized functions: a promoted entry is DATA, a *promotion record* (carrier type, member identity,
embedded-hop path, receiver adjustment, target = a declared method or an embedded interface field), whose path the core executes at dispatch.
`Func.wrapper`, the frame marker and every consumer above are deleted. **The regularity gain:** one callable shape (a declared function); no frame the
program did not write; the recover rule loses its special case; the race footprint is the path's own loads, not a body-shape recognizer; the BUG-087
family test stops riding on a frontend flag; `Frame` is born without the slot at C3.

## 2. The semantics decisions P forces

[AGENT] throughout: options, spec, gc, recommendation; "zero-change" = today's wrapper trajectory reproduced.

- **S1 Scope: which selectors the core resolves.** (a) All selectors, the ruled text read literally («the core resolves selectors and interface
  dispatch through the embedding chain»). (b) Only the dynamic surface: dispatch, satisfaction and method expressions. The static `x.M()`, `x.M` and
  type-parameter calls stay frontend projection chains plus ordinary calls, which is what they already are. spec#Selectors, spec#Calls. gc resolves
  static selectors at compile time too. **Rec (b).** (a) would add a second path to shapes that are already ordinary call rules. The logic team's
  `MaybeUpdate` pilot uses exactly those rules (§3).
- **S2 Who chooses the path.** (a) The core computes it from `FieldDef.embedded` and the method tables, following spec#Selectors «shallowest depth …
  not exactly one f … illegal» and spec#Struct_types' receiver rules. That includes FIELD-vs-method shadowing at equal depth. It is blocked below
  imported embedded types, whose fields are not on the wire: an answer there would have to refuse, and twin/corpus rows such as `raft.DefaultLogger`
  would change lane. (b) The frontend records the `go/types` selection (`types.NewMethodSet`, the typechecker's own answer). The decoder VALIDATES
  each record and fails closed. Each hop must be an embedded field of the previous hop's struct. The last hop must be the target's receiver base.
  Value/pointer set membership must follow spec#Struct_types' rule: embedding `T` gives both sets `T`-receivers and `*S` `*T`-receivers; embedding
  `*T` gives both sets both. Member identity must equal the target's, package-qualified. (c) Both, with a decode-time cross-check. **Rec (b).** Depth
  and ambiguity stay the frontend's trusted answer. They are pinned by
  `embedding/{promoted-ambiguous-not-satisfied,promoted-method-shadow,promoted-field-depth-shadow}` and
  `spec-examples-decl/selectors-embedding-depth`. (c) doubles the work for a check the differential already makes.
- **S3 When and where the path is walked.** At the ENTRY of the dispatched call, after the receiver box and arguments are evaluated. That is exactly
  when the wrapper's body walked it. So for `go i.M()` the walk happens inside the child's entry, and its reads and any panic are attributed to the
  child. This is today's spawn arm (`Multi.lean:1535`), gc's wrapper running in the child. For `defer i.M()` the walk happens at the drain, not at
  registration. For `f := i.M` it happens at each call. spec#Method_values («x is evaluated and saved during the evaluation of the method value» — for
  an interface `x` that saves the BOX, and the box's promotion path is walked when the wrapper runs). spec#Defer_statements, spec#Go_statements. gc:
  all three go through the itab to the wrapper, which walks the path when it runs. **Rec: as stated (zero-change).** The spec leaves no latitude here
  that the machine does not already pin.
- **S4 Nil in the path.** A panic happens exactly where a nil pointer is projected through: a field of `nil`, or the address `&nil.f` that
  spec#Address_operators says panics with its operand. A panic also happens where a value receiver must be copied out of `nil`. A final
  POINTER-receiver target reached through an embedded `*E` that is nil gets `nil` as its receiver, with no panic. A nil embedded INTERFACE field at
  the end of the path panics with the nil-interface dispatch text. spec#Selectors («x … nil and x.f denotes a struct field … run-time panic»),
  spec#Run_time_panics. gc's wrappers do the same (the rows `embedded-interface-shadowing/{nil-pointer-method-promoted,interface-field-nil-panic}` and
  `promoted-nil-embedded-pointer/*` pin it). **Rec: as stated (zero-change).**
- **S5 A path ending in an embedded interface field** re-dispatches as a SEPARATE machine step on the field's value, with no frame pushed. It is not
  recursion inside one step. That keeps `stepFn` structurally total. A self-embedding cycle (`*S` whose `I` field holds `s`) steps until fuel runs
  out. gc overflows its stack (fatal), and today's wrapper frames also run to fuel-out ([inf]: no stack-depth model found in `GoCore/`), so the class keeps its current lane. **Rec: yes.**
- **S6 `recover()` in a promoted method.** spec#Handling_panics: recover works when «called directly by a deferred function». gc skips
  `abi.FuncIDWrapper` frames, so `defer i.rw()` and `defer S.rw(s)` recover inside the promoted `rw`. After P no synthesized frame exists, so the real
  method's frame is the deferred frame. `recoverThroughWrappers` is replaced by a direct check that the deferred frame sits on the unrecovered
  `panicResumeK`. Its glue skip existed only for wrapper-body glue (docstring, `Machine.lean:3751`). **Rec: the direct form**, pinned by
  `interfaces/recover-promoted-wrapper/*` (8 rows, controls included). If its well-formedness lemma proves costly, fallback: keep the glue skip, which
  is equally zero-change.
- **S7 Method expressions `S.M` / `(*S).M` over a promoted M** name the promotion record as a callee. Calling the callee applies the path to argument
  0 and enters the target directly. The alternative is to lower `S.M` to a func literal. That adds a non-wrapper frame, so `defer S.M(s)` would stop
  recovering where gc does: a wrong answer. **Rec: callee = declared `Func` | promotion record.** For PROMOTED entries the `(*S).M`
  deref-adapter refusal (`emit.go:7222`) retires, because a record's adjustment can dereference. For declared value methods it stays.
- **S8 The race footprint.** A value-receiver dispatch through a `*S` box loads the path's cells, not the whole pointee. Hops through an embedded
  POINTER load the pointer field, then the pointee, which is gc's wrapper loads. Today the first shape is narrowed by `dispatchLeaf` (identical). The
  second falls back to a whole-pointee read, an over-refusal inside BUG-041's S3 addendum («no corpus case constructs one yet»). **Rec: exact loads.**
  This is THE one documented access-trace change of P. No existing row moves; the born row in §5 S0 is expected to move red→green.
- **S9 Interface satisfaction and the BUG-087 family.** Satisfaction compares against the record's target signature. The signature comes from the
  target `Func`, or from the embedded interface's `MethodSig`. For stubs it comes from an explicit signature carried with an `unsupported` cause (§4).
  The family test «not a synthesized wrapper» becomes «the resolution path is empty» (a declared method of exactly the pointee), and `nilTextFacts`
  follows. **Rec: yes (zero-change**, pinned by the BUG-087 rows and the promoted-method-set rows).
- **S10 Generics.** Nothing is forced. Instantiated structs get records from the instantiated `NewMethodSet` in the same pass that emits their
  wrappers today. A record's target stencil must be drained, so the second `drainMono` stays (F13 note, `emit.go:388`). Type-parameter calls are
  static (S1). **Rec: no change.**

## 3. The logic team's conditions, one by one

| Their condition (logic team §4, relayed) | How the design meets it ([AGENT]) |
|---|---|
| receiver evaluated once | box/argument evaluation unchanged; the path walk is a pure function of that value and the store (S3) |
| pointer/value receiver adjustment and copying | the record's `adjust` (`asIs` / `deref` / `addr`), validated at decode against spec#Struct_types (S2); a value receiver is copied at entry, as now |
| embedded-field traversal, nil behaviour | S2 path, S4 nil points, S5 interface terminal |
| package-qualified method identity | records key on `Declaration.MemberId` = the target's (decode check), e.g. twin `log.output` stays `(log, output)` |
| method-value receiver capture at creation | static method values unchanged (frontend path at creation, `promoted-method-value/{snapshot,live}`); interface method values capture the box (S3) |
| direct-recover eligibility; deferred receiver/argument capture | S6 (no synthesized frame; `defer`/`go` args evaluated at the statement, path at the call, S3) |
| expose declaration lookup + resolved receiver path/entry equations | the named set below, delivered with P, in the window's equation-lemma style (charter row 3) |

Exposed declarations (intended names, [AGENT]; all `GoCore`):
- `methodDecl?` — declaration lookup, depth 0 (the `direct` fold inlined in `concreteMethodForDynamic?` today); `promotion?` — the record lookup.
- `resolveMethod?` — replaces `concreteMethodForDynamic?`, returning `{path, target, adjust}`. Lemmas `resolveMethod?_declared`,
  `resolveMethod?_ptrDeclared` (the `*T ⊇ T` arm), `resolveMethod?_promoted`.
- `receiverAt` — the path walk over the store, returning the receiver and its loads. Lemmas `receiverAt_nil_path` (the direct path is the identity or
  the single deref, i.e. today's behaviour), `receiverAt_field`, `receiverAt_ptr`, `receiverAt_nil_panic`.
- `callee?` — replaces the callee half of `findFunctionIn?` in `enterFrame`: declared `Func` | promotion record. Lemma `enterFrame_declared`: for a
  declared callee, entry is exactly today's function-call rule, which is the `MaybeUpdate` shape.
- `recoverAtDeferred` — replaces `recoverThroughWrappers`. Lemma `recoverResult_eq`.

`findFunctionIn?` keeps its signature; its domain loses the wrapper `Func`s. `methodInfoByFuncId?` is unchanged (declared methods and anchors).
`dispatchLeaf`, `wrapperForwardArg`, `recvFieldChain`, `Cont.recoverTransparent`: deleted, no aliases. All go into the migration table.

## 4. The wire

([AGENT].) The schema moves from `golean-native-v1` to `golean-native-v2`, so a v1 wire refuses by name.
- `methods` carries DECLARED methods, anchors and imported/sync stubs only. The `"wrapper"` key leaves the allowed-key set, so a wire carrying it
  fails closed.
- A new REQUIRED top-level `promotions` array holds entries `{type, member, inPtrSetOnly, path:[{owner, field, ptr}], adjust, target: {method: FuncId}
  | {iface: TypeId}, unsupported?, sig?}`. `sig` must be present exactly when `unsupported` is (the sync-primitive and FR-23 stubs become records). An
  empty array means no promotions.
- D2 contract text: a `full` `MethodSetRecord` means declared ∪ promotion records (`methodSetCoverage?` unchanged). One record emitter replaces
  `synthesizePromotionWrappers`, `synthesizeWrapper`, `syncPromotedStub` and `promotedSigStub`.

Consequence: every corpus wire carrying a wrapper or promoted stub (≥ 182) and the twin wire change bytes. `twin-chdriver.wire.json` re-pins (53 wrappers + 3 stubs → 56
records), `scripts/check-frontend-pins` moves with a written reason, and train step 5a re-certifies. This is a provenance refresh, not a claim change,
if §5's criterion holds.

## 5. Plan

([AGENT]; `scripts/capped` throughout; the lane owner per the window plan is Fable.)
- **S0 — born pins on main, before any change** (`--diff`), each probed against go1.26.5 first: `go i.M()` over a nil embedded `*E` with a value
  method, and over a nil embedded interface field (child aborts); `defer i.M()` / `f := i.M` over a `*S` box mutated before the call (path walked
  late); `defer S.M(s)` with `recover` in the promoted `M`; a nil `*S` box calling a pointer method through a value embed; race: a `*S` box, a value
  method through an embedded-`*E` hop, a concurrent disjoint write (gc `-race` clean; expected red today, over-refusal, on BUG-041's Cases line). Any
  row red on main gets a `BUGS.md` Cases line at birth.
- **S1 — additive records + a cross-check** (`--diff`). The frontend emits `promotions` ALONGSIDE the wrappers. The decoder validates each record (S2)
  and checks that each wrapper's body path equals its record's path, failing closed on any disagreement. The machine is unchanged. This gives
  independent evidence over all 182 wires and the twin that the data equals the code it replaces.
- **S2 — the switch** (`--slow`: wire + twin re-pin). v2 schema; wrappers deleted; `resolveMethod?` / `receiverAt` / `callee?` / `recoverAtDeferred`
  in the core; `Func.wrapper` and its consumers deleted; proofs repaired (`StateWf`, `MachineSound`, `MultiSound`); the S1 cross-check retires with
  the wrappers. Detector-soundness re-run.
- **S3 — equation lemmas + records** (fast + `check-core-audit`). The §3 lemmas; the migration table; the changelog entries; the BUG-007/015/041/087
  and the method-set-contract note text moved to the record form.
- **Audit** after S3, one train. It is aimed at §2's claims and the criterion below, not at the gate.

**Zero-behaviour-change criterion.** Every existing row stays in its lane and its certified set, and the choice trace stays byte-identical. Wrapper
bodies contain no choice site: no loop back-edge, no registry op, no map iteration, no probe. The one entry-time pick, `nilValueMethodText`, stays at
the anchor. The DOCUMENTED changes, and no others: (i) the S8 access-trace narrowing on embedded-pointer hops, which moves only the S0 race row; (ii)
step and fuel accounting: a promoted dispatch no longer runs the wrapper's frame, call and return steps, so step counts fall with no pool scheduling
point lost (boundaries arise only at spawns and registry ops, `Multi.lean:556`); any record or row carrying an exact step count is listed in the S2
tail. Anything else that moves is a finding and stops the slice.

**Estimate.** 4–5 sessions: S0 ½, S1 1, S2 2–2½, S3 1. The plan's 3–4 did not include the born pins or the cross-check slice.

**Changelog** (`docs/changelog/61958f2e-WINDOW.md`, [AGENT] draft): `Func.wrapper` deleted; `Cont.frame`'s last field deleted, so every `.frame t e r
ds k w` pattern loses `w` and `entry_step`'s `hw : f.wrapper = false` disappears; `recoverThroughWrappers` → `recoverAtDeferred`;
`concreteMethodForDynamic?` → `resolveMethod?`; the callee lookup → `callee?`; `dispatchLeaf` deleted; `Program.promotions` added; the direct method
path unchanged, with equations `enterFrame_declared` and `receiverAt_nil_path`.

## 6. Decisions for the [USER]

All recommendations are [AGENT]; each item is a single sentence. G = a genuine semantics or contract choice; R = routine.

1. (G) The core resolves promotion only on the dynamic surface; static selectors stay frontend projection chains. This amends the ruled G-P wording
   (S1). Rec: YES.
2. (G) Paths come from `go/types` as decoder-validated promotion records rather than being computed in the core (S2). Rec: YES (option b).
3. (G) The path is walked at call entry: in the child for `go`, at the drain for `defer`, at each call for interface method values (S3). Rec: YES.
4. (G) Nil points are as in S4, and an interface-terminal path re-dispatches as its own step (S5). Rec: YES.
5. (G) Promoted method expressions call the record directly rather than a synthesized closure, preserving recover (S7). Rec: YES.
6. (G) The race footprint of embedded-pointer hops becomes gc's exact loads, the one documented trace change (S8). Rec: YES.
7. (R) `recoverThroughWrappers` becomes the direct `recoverAtDeferred`, with the glue-skip fallback (S6). Rec: YES.
8. (R) Accept the step/fuel accounting shift, as the C5 precedent did, with any count-carrying record listed (§5 ii). Rec: YES.
9. (R) Wire v2: `promotions` required, `wrapper` refused, twin re-pin under `--slow` (§4). Rec: YES.
10. (R) Plan S0–S3 with the S1 additive cross-check, 4–5 sessions (§5). Rec: YES.
