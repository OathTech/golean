# Audit: train 20's struct retag at dereference and in the normalizer

[AGENT auditor], 2026-10-26. Pre-merge adversarial audit of branch `stage/train-20-1026` at
`6a65dd6f` (six commits over main `6e05137a`), focused on commit `8c87b3ce` — the only commit of
the train that touches `GoLean/` or `Tests/`: the whole-struct value through a struct-pointer
conversion (BUG-134) and the enumeration driver's deadlock classification (shake review F3).
Independent of the lane's report; every number below was re-measured here. Probes:
`docs/reviews/2026-10-26-train20-audit-probes/core/` (one `main.go` per directory, `probe()` the
observed function, `main` prints it for gc).

## Verdict

**Ships.** On every legal Go program probed — the 60 new rows (fresh run, both sides, 60/60
PASS) and 27 probes of my own across the routes the brief names — the machine agrees with gc
byte for byte, the three proof repairs leave every kept statement intact (`scripts/gen-contract
--check`, kernel replay and `lake comparator` all PASS at the tip), and the red-at-base claim is
true where I checked it. Two findings are worth the owner's attention at the merge ask, neither
a wrong answer against gc: **F1 (medium)** — the write-side retag sits in the general normalizer,
so a wire that carries NO conversion (a malformed wire) is now absorbed where the base refused it
by name, a narrowing of the fail-closed surface that the BUGS entry describes with an overclaim;
**F2 (low)** — the compatibility predicate is blind to the declaring package of unexported field
names, unreachable through a type-checked wire. F3 collects documentation slips. None must change
before merge; F1 is a doctrine trade-off for the owner to rule on (fix or record), with a concrete
narrower placement sketched below.

## What the commit does (as read, not as reported)

- `GoLean/GoCore/Ops.lean:2318` `TypeEnv.structTagCompatible`: two `TypeId`s are compatible
  exactly when both resolve to `.struct` entries with equal wire `FieldDef` lists (`name`, `typ`,
  `embedded`; tags are not on the wire). `Ops.lean:2562` `structTagCompatible ctx` is the same
  predicate at `ctx.types`, unchanged in meaning for the three L7 field arms.
- `Ops.lean:2337` `retagStruct types name v`: a `.struct actual fields` with `actual ≠ name` and
  the two compatible becomes `.struct name fields`; everything else is returned as is.
- The READ side, `GoLean/GoCore/Machine.lean:508`: the `.deref ty` strict apply returns
  `derefRetag ctx ty x` (`Ops.lean:2577`): when `ty` resolves to `.struct name _`, the loaded value
  is `retagStruct`ed to `name`. Every frontend emission site of a `deref` node passes go/types'
  static pointee type (`tools/nativefrontend/emit.go` 4511, 4924, 6050, 6112, 6174, 6583, 7095,
  7484, 8476; `unseq_lower.go` 286), so `ty` IS the type Go gives `*p`.
- The WRITE side, `Ops.lean:2426`: `normalizeValueForTyAt`'s struct arm normalizes
  `retagStruct types name value` instead of `value`, so every normalization at a declared struct
  type — `writeAt`'s leaf (the cell store), `Store.alloc` (declarations), `bindParams`, map keys
  and values, channel elements — accepts a compatible tag and emits the declared one.
- Proofs: `StateWf.lean:1298` `retagStruct_locSup`, `:1304` `derefRetag_locSup` (new; sound by
  inspection — the retag keeps the field array, so `locSup` is unchanged, and `derefRetag` is the
  retag or the identity); `normalizeValueForTyAt_locSup` composes the new equality;
  `normalizeValueForTyAt_isNormal` (`:2062`) generalizes the retagged value before the case split
  — sound because the statement constrains only the OUTPUT `w`; `applyStrictOp_wf`'s deref arm
  rewrites with `derefRetag_locSup`; `TableMonotonicity.lean:407–408` `derefRetag_free`/`_eq` by
  `rfl` (the definition reads only `ctx.types`) and the `free_rw` sets extended. Statements of
  the four repaired theorems are textually unchanged in the diff.
- Part (2): `GoLean/CLI.lean` `enumPoolRun` throws `deadlockStop pctx m.shared m.threads`
  (`Multi.lean:388`, the definition behind `deadlockOrRefusal`, which both drivers use);
  `ChoiceTrace.lean`'s `poolLoop` reports `deadlockStop`'s status; `Tests/GoCoreEval.lean`
  `malformedParkedStateFacts` pins the mirror. The eval tests run at the tip: 431 ok, 0 not ok.

## Findings

### F1 (medium) — the write-side retag absorbs a wire with no conversion where the base refused it

**What.** `retagStruct` is applied inside `normalizeValueForTyAt` (`Ops.lean:2426`), i.e. at
every site that normalizes a value at a declared struct type, not only at the one place a legal
Go program needs it (a store through a converted pointer, where the CELL's mint tag legitimately
differs from the store target's static type). A value whose tag merely matches the declared
type's field list is now accepted by `Store.alloc`, `bindParams`, the map-key, map-value and
channel-element normalizations and the cell store alike.

**Reproduction** (`core/p10-wire-no-conversion/`): the program declares `var b B = B{1, 2}` and
observes `b` by a type switch and `==`. Lower it; in the wire set the literal's `target`/`type`
to `main.A` while the declaration's type stays `main.B` (a simulated frontend tagging fault; no
conversion anywhere). The base binary (main `6e05137a`) answers
`{"status":"stuck","message":"struct value type mismatch: expected main.B, got main.A"}`;
the tip answers `{"status":"ok","values":[12]}`.

**Why it matters.** For a type-checked wire this cannot happen: go/types requires a conversion
wherever a named struct value meets a slot of another named type, and the frontend lowers that
conversion as a `.deref ty` at the pointer's type or a value conversion (`convertValueToTy`), so
no legal program's answer changes — I found none (below). But the charter's doctrine is that a
wire outside the lowering contract is refused by name, never absorbed, and the base's `stuck`
was exactly that signal. BUG-134's entry argues the retag «is observationally the explicit
conversion» so «a tag a frontend could have failed to convert is not absorbed into a different
answer». That holds for a MISSING conversion; it does not hold for a wrong DECLARED type (a
`var b B` where the source said `A`): the box built from `b` takes its dynamic type from the
wire's static type, so a type switch or an interface comparison answers for `B` — a different
answer with status `ok` — where the base stopped at the declaration with the mismatch named.
The absorption also composes with F2 (a cross-package pair reads compatible on the wire).

**Severity.** Medium: no gc disagreement on any legal program; a reduction of the fail-closed
surface on malformed wires, contrary to the doctrine as written, and the BUGS text overstates
the safety argument. Not merge-blocking on correctness; it is the owner's call whether the
doctrine admits this exception (record it in BUG-134 and the entry's safety sentence corrected)
or the placement is narrowed.

**A narrower placement, if the doctrine is to hold.** Retag only where the mint tag
legitimately differs from the static type: (i) the `.deref ty` apply, as now; (ii) the cell
boundary — `writeAt`'s leaf arm (`Ops.lean:2768`) normalizing `derefRetag ctx ty v` at the
cell's declared `ty`; (iii) the pointee read of a value-receiver dispatch (`receiverAt`'s
`.deref` and `.cell` arms, `Ops.lean:5193`, or its caller) at the receiver's static type, which
`bindParams` then sees already tagged. `Store.alloc`, `bindParams`, the map and channel
normalizations stay strict. The unseq lane's `unseqReadTarget` (`Machine.lean:2431`, a bare
`Mem.load`) lands in a binder cell declared at the occurrence's type, so (ii) covers it. The kept
statements `storeLoc_root` (`Equations.lean:233`) and `bindParams_cons` keep `normalizeValueForTy`
as their hypothesis; under (ii) `storeLoc_root` should still hold as stated, since a value the
strict normalizer accepts at `ty` already carries `ty`'s tag and the retag is then the identity
(`retagStruct_self`) — a proof obligation, not a statement change, but I have not discharged it.
Cost: moderate (two sites plus `HeapNormal`/`isNormal` lockstep). I would not hold the train for
it; the ruling should be recorded either way.

### F2 (low) — the predicate ignores the declaring package of unexported field names

**What.** `TypeEnv.structTagCompatible` compares wire `FieldDef`s, and the frontend emits field
names unqualified (`emit.go:1987`, `fld.Name()`). spec#Type_identity: «Non-exported field names
from different packages are always different», so `sub.A{x int; Y int}` and `main.C{x int; Y
int}` are NOT identical and `(*C)(pa)` is illegal — yet their wire `FieldDef` lists are equal.

**Reproduction** (`core/p11-cross-pkg-negative/`): gc `cannot convert pa (variable of type
*sub.A) to type *C`; the frontend refuses with the same go/types text, so no wire exists. The
positive half (`core/p11-cross-pkg/`: the conversion inside `sub` between its own two types,
dereferenced whole in `main`) agrees, `131` both sides. The wire of the positive probe shows
`sub.A`, `sub.B` and `main.C` with identical field lists `[(x, false), (Y, false)]`.

**Why it matters.** Unreachable through a type-checked wire, so no fidelity consequence today;
it widens F1's absorption to cross-package pairs on a malformed wire, and the predicate's
docstring claims spec-exactness («identical underlying types ignoring tags»), which is true of
the per-field comparison but not of this clause. Remedy: carry the package on unexported field
names (a wire change) or state the over-approximation in the docstring and in BUG-134's
predicate paragraph. Blank fields (`_`) are the same clause; `core/p05-blank-and-unexported/`
shows the same-package case right (`314` both sides).

### F3 (low) — documentation slips

1. BUG-134's safety sentence (quoted under F1) overclaims; see F1 for the counter-case.
2. The commit message and BUG-134 list `isNormalForTyAt_sound` among the repaired proofs; its
   text is unchanged in the diff (the new `@[simp] retagStruct_self` discharges the new goal
   inside the existing `simp`). Harmless, but a reader checking the diff will not find it.
3. `Corpus/coverage/exec/pointers/struct-through-conversion-store/cases.tsv`'s header names the
   green-at-base controls as «promoted-set, the first half of nested-store», while the commit
   message and BUG-134 name the train's three controls as `boxed-type-differs`, `swap`,
   `promoted-set`. Both are true of different things (a row vs. a half of a row); the header
   should say which rows were green, since `nested-store` as a row was red.

## Checked and found sound

- **Spec fit of the predicate on everything but F2.** The wire carries the parts of struct
  identity the conversion rule needs: names, types (`Ty` structural equality: pointer, slice,
  array, map, chan, func, interface and named leaves — `core/p06-field-kinds/` `123967` both
  sides; parameter names are not on a `funcType`, `core/p35-func-field-names/` `61103` both
  sides), embeddedness (compared, as go/types does even under `IdenticalIgnoreTags`), field
  order (array equality), tags (stripped, as the conversion rule ignores them —
  `shapes/tag-only`, `store/tag-only`). Fields of distinct named types with identical shapes
  (`Next *A` vs `Next *B`, `V A` vs `V B`) compare unequal, matching Go's refusal to convert;
  recursive types therefore never retag across names. Generic instantiations are monomorphized
  to their own struct entries (`mono.go:548`), so `(*H[int])(&g)` for `G[int]`/`H[int]` works and
  `G[A]`/`G[B]` differ (`core/p03-generics/` `11118` both sides). `type C B` is emitted as its own
  struct entry with B's fields (`emit.go:1973`), so `resolve` returns `C`'s own name and the
  retag lands on `C`, not `B` (`shapes/defined-over-defined` PASS). A true alias `type BB = B`
  never reaches the table (`core/p32-alias-type/` `12` both sides).
- **Methods and boxes.** A box takes its dynamic type from the wire's static type at the
  `.toInterface` apply (`Machine.lean:534–543`), never from the value's tag; type assertion
  compares `dynTy` (`Ops.lean:3562`); dispatch resolves on `dynTy` (`dynamicDispatch?`,
  `Ops.lean:5355`) and the value receiver is read whole by `receiverAt` then normalized at the
  receiver type by `bindParams` (`Machine.lean:912`), where the write-side retag applies. So a
  value converted to a type with a different method set and boxed carries the new type and its
  methods: `core/p01-methods-box/` (`A` has no methods, `B` has `M` and a mutating value
  receiver) `BByn21` both sides; `core/p22-method-value-mutation/` (a value-receiver method value
  copies at binding time, a pointer-receiver one sees the later write) `310` both sides;
  `core/p27-type-switch-binding/` `111`; `core/p08-iface-switch-eq/` `121`;
  `core/p34-empty-struct/` `110` (two empty named types: equal through the alias, boxes unequal).
- **The read side's `ty` at every deref shape.** Pointer to a struct field that is itself a
  struct (`shapes/inner-field`, `store/inner-field`, `core/p21-outer-then-inner-alias/` `1`),
  array and slice elements (`shapes/array-elem`, `store/array-elem`, `store/slice-elem`), a
  pointer from an interface or a map (`core/p04-iface-held-pointer/` `112`;
  `shapes/stored-pointer-later`), `new` and a literal's address (`store/new-and-literal`,
  `shapes/double-pointer`), a pointer to a pointer (`.ptr` resolves to a plain body, no retag,
  then the inner deref retags — `**ppb` rows), a converted pointer returned from a function
  (`core/p26-func-returning-converted/` `113`), an embedded `*A` converted (`core/p17-embedded-by-pointer/`
  `145`), a defined non-struct pointee (`core/p16-defined-nonstruct/` `27`: `resolve` yields a
  plain body, the value is untouched, the box's type is the static one), a captured variable's
  deref (`emit.go:8476`, `core/p20-closure-capture/` `312`), the per-iteration range copy
  (`emit.go:4511`). A pointer to an array of structs cannot be converted across element names
  (`[2]A` ≠ `[2]B`), so no retag is needed there and none fires (`resolve` on `.array` is plain).
  Type parameters never reach a deref: the wire is monomorphized.
- **The unseq lane.** `core/p02-unseq/`: three statements lower as `unseq` graphs (the wire has
  three `"stmt": "unseq"` nodes; the machine consulted 4 choice sites) with `*pb` as a call
  operand beside `bump()`, `(*pb).Y` in a sweep, and `*pb = B{bump(), (*pb).Y}` as a frozen
  target with a call on the right — `11432` both sides. The sweep's binder cell is declared at
  the occurrence's static type, so the bare `Mem.load` of `unseqReadTarget` is retagged at the
  binder store.
- **BUG-133's identity, the detector, the dedup engine, the seed loader, the readout.** `Loc`s are
  untouched by the retag; `valueEq`'s pointer arm compares `canon` as before (`value/neq-and-ptr-eq`,
  `shapes/chained`, `core/p28-holder-eq/` `10`: two holders of the alias equal, a `*B` box and a
  `*A` box unequal). The detector keys the same loads and stores (`Mem.loadFor`, `Mem.store`);
  `core/p12-race/` (a whole store through the alias against a whole read of the original) is
  `race` on the machine and `WARNING: DATA RACE` under gc `-race`; the synchronized twin
  `core/p25-goroutine-store/` is `98` both sides. `GoValue.eqb` (`Value.lean:971`) feeds only
  `StateEqb`/`EnumDedupCheck`, the enumeration's structural state equality: a retagged in-flight
  value and the cell's value sit in different positions of a state and are never compared to each
  other; two tapes whose states differ only in a tag are treated as distinct — an
  over-approximation of distinctness that costs enumeration work, never an answer. The seed
  loader builds struct values at the DECLARED name (`Seed.lean:179–182`), so a seed cannot carry
  a wrong tag; the readout renders the value's tag, which the retag makes right
  (`value/returned`: `typeName` `B` on both sides).
- **Contract and proofs.** `scripts/gen-contract --check` PASS (385 kept theorems, §D pins 56 ⊆
  contract, no regeneration); `scripts/check-kernel-replay` PASS (55 modules, 11.2 s);
  `scripts/check-comparator` PASS (no sandbox, 29 s, «Your solution is okay!»);
  `.lake/build/bin/gocore-eval-tests` 431 ok / 0 not ok. The baseline diff of `8c87b3ce` is the
  count header and 60 added rows; no existing row changed (`git show 8c87b3ce --
  baselines/native-full.tsv`: one `-` line, the header).
- **The rows.** All 60 ids through `scripts/diff-one` at the tip: `cases=60 pass=60 fail=0`,
  fresh both sides (`.tmp/all60.log`, deleted). Red-at-base, measured by lowering the three
  `main.go`s with the tip frontend and running the base binary (`/home/mike/projects/golean/.lake/build/bin/golean`,
  built at main `6e05137a` after its commit time): `value/eqLiteral` `stuck` («left struct
  equality type mismatch: expected main.B, got main.A»), `value/returned` `stuck`,
  `store/storeOnly` `before` then `stuck` («expected main.A, got main.B»),
  `shapes/definedOverDefined` `stuck` (`main.C` vs `main.A`), `shapes/valueReceiver` `stuck`,
  `shapes/tagOnly` `stuck` (`main.TB` vs `main.TA`); the three controls `value/boxedTypeDiffers`
  (`false`), `store/swap` (`31`), `store/promotedSet` (`5`) green at the base — as the lane
  reported.
- **The frontier stays refused by name.** `core/p14-anon-struct/`: `(*struct{ X, Y int })(&a)`
  is `unsupported` «frontend-quarantined: anonymous non-empty struct type» (gc `1`) — FR-13,
  unchanged; a non-compatible tag at a deref is left untouched and refused downstream as before.
- **Part (2).** `deadlockStop` is the one definition behind `deadlockOrRefusal`
  (`Multi.lean:388–397`), which `stepMulti` and both drivers use (`:1753`, `:1996`); the CLI
  mirror and the choice-trace mirror now call it. The new eval facts pass; `enumInitRun`'s
  `.deadlock`s are the sequential init driver's arm and were rightly left alone.

## Reproduction

```
# in a worktree at the stage tip, .lake built, deps linked
GO111MODULE=off go build -o .tmp/nativefrontend ./tools/nativefrontend
P=docs/reviews/2026-10-26-train20-audit-probes/core
.tmp/nativefrontend --dir $P/p10-wire-no-conversion --out .tmp/p10.json
# edit .tmp/p10.json: in funcs[name=probe].body.body[0].decls[0].init set target/type to main.A
.lake/build/bin/golean native-json-run --input .tmp/p10-edited.json --function probe   # tip: ok 12
/home/mike/projects/golean/.lake/build/bin/golean native-json-run --input .tmp/p10-edited.json --function probe   # base: stuck
(cd $P/p11-cross-pkg-negative && GO111MODULE=off GOWORK=off go run .)   # cannot convert
mkdir -p .tmp/gp/src && ln -s $PWD/$P/p11-cross-pkg/sub .tmp/gp/src/sub
(cd $P/p11-cross-pkg && GOPATH=$PWD/../../../../../.tmp/gp GO111MODULE=off GOWORK=off go run .)   # 131
xargs -a <ids of the 60 rows> scripts/diff-one   # 60/60 PASS
```

Worktree: `/home/mike/projects/golean/.claude/worktrees/audit20-core-1026` (left in place, with
its copied `.lake` — a candidate for deletion once the train lands).
