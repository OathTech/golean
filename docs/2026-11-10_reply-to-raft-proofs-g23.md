# Reply to raft-proofs' ask G23: the `.interface` arm is closed, `recoverAtDeferred_none` is contracted

2026-11-10, [AGENT] lane `core/g23-iface-normal-1110` for GoLean, answering the two asks relayed
by the [USER] 2026-11-10 (the pair is G23 on our side). The pin to consume: GoLean `main` at the
commit that lands this lane, or later (the one-level form: lane `core/g23-bplus-1125`; the deep
form's branch `core/g23-iface-normal-1110` never landed; toolchain `leanprover/lean4:v4.35.0`). Earlier replies:
`docs/2026-10-27_reply-to-raft-proofs-g21.md` (G21), `docs/2026-10-27_reply-to-raft-proofs-g22.md`
(G22). Both halves are done. No row of the differential corpus changed its answer. The comparator
contract gained exactly TWO statements (475 → 477) and no kept statement changed its text
(§ The contract).

> **REWORKED 2026-11-25 — the box check is ONE LEVEL deep** ([USER] ruling 2026-11-25, on your
> answer of the same day that the constructor check is what you need, the head check welcome and
> the deep property unused). As first built (2026-11-10) the walk entered every payload and
> required it normal at its dynamic type, recursively; the independent audit's F1 stood against
> that: the store-time guard re-walked a payload at every cell birth, bind and store — linear
> per interface store, quadratic on value-nested boxes (main's binary vs that build:
> `deep(16000)` 0.56 s → 22.3 s, `consList(12000)` 0.78 s → 72.2 s, `bigBox(800)` 0.11 s →
> 8.0 s). The walk now checks a payload's HEAD and stops: it never enters a payload. This
> document describes the reworked design throughout; the lane is `core/g23-bplus-1125`, G23's
> commits replayed on `main` after the dead-cell landing, and the pin to consume is the commit
> that lands it. G23 (2) is unaffected.

## G23 (1) — the `.interface` arm of the normal form is closed: DONE

`isNormalForTyTy` ended its interface case in `| .interface _, _ => true` and the normalizer in
`| .interface _, value => return value`. Both are closed, in two layers.

**The constructor check** (the arm itself, `GoLean/GoCore/Ops.lean`, in lockstep arm for arm):

```lean
-- normalizeValueForTyTy
| .interface _, .nil => return .nil
| .interface _, .interface dyn value => return .interface dyn value
| .interface _, value => stuck s!"expected interface value, got {repr value}"
-- isNormalForTyTy
| .interface _, .nil => true
| .interface _, .interface _ _ => true
| .interface _, _ => false
```

**The head check at the dynamic type** (new, beside the public pair; one level):

```lean
def boxHeadTy : Ty → GoValue → Bool          -- the head of the normal form at a non-named type:
  | .int kind, .int value k => decide (kind.normalize value = value) && decide (kind = k)
  | .float kind, .float bits k => decide (kind.normalizeBits bits = bits) && decide (kind = k)
  | .array length _, .array values => decide (values.size = length)      -- the LENGTH only
  | .pointer _, .addr _ | .pointer _, .nil => true
  | .slice _, .slice _ | .map _ _, .map _ | .chan _ _, .chan _ => true
  | .bool, .bool _ | .string, .string _ => true
  | .funcType _ _ _, .funcVal _ _ | .funcType _ _ _, .nil => true
  | .sync kind, .syncData p => p.kind == kind
  | _, _ => false                             -- every other pair, spelled out arm by arm in the source

def boxHeadAt (types : TypeEnv) : Nat → TypeIdx → GoValue → Bool   -- a NAMED dynamic type
  | 0, _, _ => false
  | bound + 1, i, w =>
      match types[i]? with
      | some (name, .struct fields) =>
          match w with
          | .struct actual fieldsValue => decide (actual = name) && decide (fieldsValue.size = fields.size)
          | _ => false                                                     -- the TAG and field COUNT only
      | some (_, .defined (.defined j)) => boxHeadAt types bound j w
      | some (_, .defined target) => boxHeadTy target w
      | some (_, .opaqueDecl _) => true
      | some (_, .interfaceDef _) => false
      | none => false

def boxHeadNormal (types : TypeEnv) : Ty → GoValue → Bool
  | .interface _, _ => false
  | .defined i, w =>
      boxHeadAt types types.size i w
        || (decide (i = runtimeErrorTypeIdx) && match w with | .string _ => true | _ => false)
  | dyn, w => boxHeadTy dyn w

def GoValue.boxesNormal (types : TypeEnv) : GoValue → Bool   -- mutual, structural on the value
  | .interface dyn w => boxHeadNormal types dyn w              -- the walk STOPS here
  | .struct _ fields => boxesNormalFields types fields.toList
  | .array values => boxesNormalList types values.toList
  | _ => true            -- the other eleven constructors, spelled out in the source

def isNormalForTy (types : TypeEnv) (ty : Ty) (value : GoValue) : Bool :=
  isNormalForTyTy (isNormalForTyAt types types.size) ty value && GoValue.boxesNormal types value

def boxesGuard (value : GoValue) : Except Stop GoValue :=
  if GoValue.boxesNormal ctx.types value then return value
  else stuck s!"expected interface value, got a box whose payload's head does not agree with its dynamic type: {repr value}"

def normalizeValueForTy (ty : Ty) (value : GoValue) : Except Stop GoValue := do
  let w ← normalizeValueForTyTy (normalizeValueForTyAt ctx.types ctx.types.size) ty value
  boxesGuard ctx w
```

and `writeAt`'s leaf arm normalizes at the descended type and then passes the same guard. So
every box the walk MEETS in a value cell — at the top, in an array element, in a struct field —
holds a payload whose head agrees with the box's dynamic type: the constructor the normal form
at that type has, with what the constructor alone carries (a number's kind and width, an
array's length, a struct's tag and field count, a sync primitive's kind). That is the whole
normal form for a scalar or reference dynamic type — a number, a bool, a string, a pointer, a
slice, map, channel or func value IS its head — and only the head for a boxed struct or array:
its fields and elements, and any box inside it, are NOT looked at. The walk does not enter a
payload, so a store costs what the type-directed normalization of the same value already cost.
`StateWf ctx σ` is still `Store.locSup σ ≤ σ.nextAddr ∧ HeapNormal ctx σ`, `HeapCell.normal`'s
value arm is still `isNormalForTy types ty v`, and all of it is still a structural `Bool`,
kernel-reducible (`decide` on a concrete store works; the §A pins below are decided that way).

The characterisation you asked for:

```lean
theorem isNormalForTy_interface :
    isNormalForTy types (.interface n) v = true ↔
      v = .nil ∨ ∃ dyn w, v = .interface dyn w ∧ boxHeadNormal types dyn w = true
```

and a store into an interface-typed cell keeps it (`HeapNormal.of_storeLoc`, `storeLoc_wf`,
unchanged statements). The other direction — the head check refuses no normal payload — is
`boxHeadNormal_of_isNormal`: a value normal at a non-interface dynamic type passes, over a table
with no ALIAS of an interface type (`boxHeadTy_of_isNormalForTyTy`, `boxHeadAt_of_isNormalForTyAt`
beneath it). That alias is the one input the head check refuses and the deep form admitted; the
frontend emits a named interface as an interface declaration, so no lowered program has one.

What an interface slot and a box may hold, from the producers (every one read; the full corpus
run unchanged):

| Where | admitted | refused, by name | evidence |
|---|---|---|---|
| an interface slot | `.nil` (the nil interface) | | `defaultValueTy (.interface _) = .nil`; the typed nil literal `.nilLit (some (.interface _)) = .nil`; the frontend leaves an untyped `nil` bare exactly when the slot is an interface (`wrapInterfaceConversion`, `emit.go`); a failed comma-ok assertion to an interface target returns `defaultValue`; `recover()` outside a panic returns `.nil` |
| an interface slot | `.interface dyn v` (a box) | | the `.toInterface` arm builds it (and passes an interface-typed source through unchanged); a type assertion to an interface target returns the box it was given; the machine's panic payloads (`runtimeErrorValue`, `stringPanicValue`) and a recovered payload are boxes; the conversion arm passes a box or nil and already refused a raw value («raw value reached interface conversion») |
| an interface slot | | every other constructor: `stuck "expected interface value, got …"` | no producer emits one; the seed loader refuses an interface type by name, so no seeded cell is involved |
| a box's payload at `dyn` | a value whose HEAD is the normal form's at `dyn` (the G21 table's constructors, a number of the right kind and width, an array of the right length, a declared struct by tag and field count, an alias through the table) | a wrong head: `stuck "expected interface value, got a box whose payload's head does not agree with its dynamic type: …"` | `.toInterface` boxes an operand of static type `dyn`; operands are built by the normalizing constructors (`buildStructValue`, `buildArrayValue`, the conversion arms) or loaded from normal cells |
| a box at an interface `dyn` | | refused | Go never double-boxes: `.toInterface` returns its operand when the checked dynamic type is an interface |
| a box at an OPAQUE `dyn` (`.defined i` whose table entry is `.opaqueDecl`) | any payload, UNCHECKED | | an imported named type the frontend carries by name only has no declared structure; a value of it IS boxed by programs the corpus answers as gc does (`time.Duration` as an int64, `sort.IntSlice` as a slice); the runtime-error payload's reserved entry (index `runtimeErrorTypeIdx`) is the same case |
| a box at index `runtimeErrorTypeIdx` over a table without the reserved entries | a `.string` payload | anything else | `runtimeErrorValue` builds `.interface (.defined runtimeErrorTypeIdx) (.string …)` whatever the table is (a hand-built or sliced table) |

Design points taken ([AGENT], 2026-11-10; each is one arm or one definition to switch if the
owner rules otherwise):

- **The head check is a walk on the VALUE, beside the public pair — not an arm of the type layer.**
  The dynamic type is read from the value and may name any table index, and the `…TyTy` layer
  carries no table; a head check inside `isNormalForTyTy` would have needed a new parameter on
  the `…TyTy` / `…At` layers (every statement over them changes, yours in `Sym/TypedWrite.lean`
  included). The walk recurses on the value's arrays and struct fields, stops at a box, and
  follows a named dynamic type's alias chain at bound `types.size`; the layers keep their
  signatures.
  Its cost to you is stated plainly: `isNormalForTy` and `normalizeValueForTy` have one more
  step when UNFOLDED, at every type, not only at interface types. A proof that evaluates
  `normalizeValueForTy` on a concrete value by `simp only [normalizeValueForTy,
  normalizeValueForTyTy, …]` needs `boxesGuard, GoValue.boxesNormal` (and `boxesNormalList` /
  `boxesNormalFields` for an aggregate) in its set; one that shows `isNormalForTy` needs the
  second conjunct. Proofs that go through `isNormalForTy_sound`, `normalizeValueForTy_isNormal`,
  `storeLoc_root` or `HeapNormal.of_storeLoc` do not see the change.
- **A box with the wrong head is refused, never repaired.** The normalizer does not rewrite a box.
  `.toInterface` boxes its operand without normalizing it, so the invariant holds because the
  store sites enforce it, and a box whose payload is, say, a raw `.nil` at a slice, map or
  channel dynamic type is refused at its first store rather than canonicalized (the G21 arms DO
  canonicalize a raw `.nil` at such a SLOT). The reason no run stores such a box (corrected at
  the audit, F4): the frontend types an untyped `nil` only for slice, map and pointer slots —
  `wrapInterfaceConversion` (`tools/nativefrontend/emit.go`) keeps the BARE nil for func- and
  chan-typed slots — but every such flow passes a normalizing store before it can be boxed (a
  result cell, a parameter, a variable, an element: the G21 chan arm canonicalizes there), so
  the operand `.toInterface` sees is already the canonical nil. Repairing instead is a larger
  change (the walk would return a value, with its own lockstep family).
- **An opaque dynamic type's payload is unchecked.** This one was FOUND, not designed: the first
  cut refused it, and the full corpus run moved two rows that box imported named types
  (`interfaces/sweep-s5-imported-carriers/duration-stringer`, PASS → stuck;
  `maps/imported-named-key-unhashable`, its named refusal → stuck). The rule was corrected and
  the rows are back, with no baseline touched. It is the one place where `HeapNormal` says
  nothing even about a box's head; for your programs it matters only if a boxed value's type is
  an opaque entry of the table.
- **`Ty.stepDown` keeps its identity arm at `.interface`**, as at G21's five types: a path write
  INTO an interface-declared cell is impossible under `HeapNormal` now, and on a non-normal
  store the leaf normalization refuses by name («expected interface value, got …»).

Re-proved with their statements unchanged (`GoLean/GoCore/StateWf.lean`): `isNormalForTyTy_sound`,
`normalizeValueForTyTy_isNormal`, `normalizeValueForTyTy_locSup`, `isNormalForTy_sound`,
`normalizeValueForTy_isNormal`, `normalizeValueForTy_locSup`, `writeAt_locSup`,
`writeAt_isNormal`, `writeAt_isNormal_array` / `writeAt_isNormal_struct` (at `.interface` no
`.array`/`.struct` root is normal, so those cases close by contradiction, as at G21),
`HeapNormal.of_storeLoc`, `storeLoc_wf`, and everything downstream: the G16 table-monotonicity
family (one new congruence, `boxesGuard_eq`; the type table is table-free, so the lifts are
unaffected) and the G22 preservation family needed nothing; the strictness and no-panic proofs
(`StepErrors.lean`, `StepFnFacts.lean`) gained `boxesGuard_strict` and `boxesGuard_noPanic`. No
theorem's statement changed anywhere.

New, for your side:

```lean
theorem boxesGuard_ok : boxesGuard ctx w = .ok r ↔ r = w ∧ GoValue.boxesNormal ctx.types w = true
theorem normalizeValueForTy_ok :
    normalizeValueForTy ctx ty v = .ok w ↔
      normalizeValueForTyTy (normalizeValueForTyAt ctx.types ctx.types.size) ty v = .ok w
        ∧ GoValue.boxesNormal ctx.types w = true
theorem boxesNormalList_iff : boxesNormalList types l = true ↔ ∀ v ∈ l, GoValue.boxesNormal types v = true
theorem boxesNormalFields_iff : boxesNormalFields types l = true ↔ ∀ p ∈ l, GoValue.boxesNormal types p.2 = true
theorem GoValue.boxesNormal_array : GoValue.boxesNormal types (.array values) = true ↔ ∀ v ∈ values.toList, …
theorem GoValue.boxesNormal_struct : GoValue.boxesNormal types (.struct tid fields) = true ↔ ∀ p ∈ fields.toList, …
theorem writeAt_boxesNormal :
    GoValue.boxesNormal ctx.types root = true → writeAt ctx b ty root path v = .ok root' →
      GoValue.boxesNormal ctx.types root' = true
```

`writeAt_boxesNormal` is the twin of `writeAt_isNormal` your `TypedWrite` mirrors: a path write
keeps the head check of the root's boxes because the leaf passed the guard. For a box-free value (every
constructor but `.interface`, `.struct`, `.array`) `GoValue.boxesNormal` is `true` by `rfl`.

Pins. `Tests/GoCoreContract.lean` §A: the four pins that asserted the OPEN arm
(`iface_cell_path_write_normal`, `_array`, `_struct`, `_preserves_normal`; C1 audit F3; never in
the comparator contract) are inverted on the same stores as `iface_cell_not_normal` and
`iface_cell_path_write_refuses`; new, kernel-decided: `iface_raw_value_refused` (an interface
cell holding `.int 7` is `¬ StateWf`), `iface_boxes_admitted` (nil, a box, a box of an array of
boxes, the runtime-error payload), `iface_box_payload_refused` (a wrong head at the top, a
double box), `iface_nested_payload_not_checked` (a bad box INSIDE a payload is not looked at). `Tests/GoCoreEval.lean` `g23IfaceNormalTests`: the two admitted
constructors; every raw constructor refused by name; per dynamic type (bool, int with range and
with kind, float, string, slice, map, chan, pointer, func, array, sync, a declared struct by tag
and by field count, a declared alias) a right-headed payload passing unchanged and a wrong-headed one refused
by name; the opaque and reserved-index rules; the interface, unsupported and unknown dynamic
types refused; the one-level rule (a bad box inside a boxed array, a boxed struct or 40 levels down a list is not looked at; a boxed struct's ill-typed field is not; its tag, count and an array's length are);
`HeapNormal`/`StateWf` on refused and admitted heaps; `Store.alloc`, the whole-cell store and
the path write refusing at the write, and a good box landing with the store still `StateWf`.

## G23 (2) — `recoverAtDeferred_none` is in the comparator contract: DONE

```lean
theorem GoLean.Contract.GoCore.Machine.recoverAtDeferred_none :
    ∀ {c : Cont},
      (∀ (chain : List PanicEntry) (k : Cont), c ≠ Cont.panicResumeK chain k) →
        recoverAtDeferred c = none
```

frozen as text in `Contract/Challenge.lean`, judged against `GoLean.GoCore.Machine.recoverAtDeferred_none`
(`GoLean/GoCore/Machine.lean`, unchanged) through the generated alias; family `recover` of
`scripts/contract-names.lean`, an explicit one-name list. It is also pinned in
`Tests/GoCoreContract.lean` §D and required by the core audit.

Its neighbours are NOT in the contract and were not added unasked. The ones you would plausibly
want next, since your tree already names three of them: `recoverResult_frame` (the frame rule:
`recoverAtDeferred` on the frame's tail decides), `recoverResult_eq` (the frame directly on the
marker), `recoverResult_cons_glue` (the walk through glue, in list form), and beside them
`recoverAtDeferred_marker` (the other half of the statement you asked for) and
`recoverResult_frame_none`. Already contracted, through the equation family: `evalE_recoverCall`,
`next_panicResumeK_recovered`, `next_panicResumeK_unrecovered`. Name the ones you want and they
go in the same way.

## The contract

`comparator.json` has 477 `theorem_names` (475 after the dead-cell landing of 2026-11-24). The
delta is exactly two ADDED statements, `GoLean.Contract.GoCore.Machine.recoverAtDeferred_none`
and `GoLean.Contract.GoCore.isNormalForTy_interface`; no kept statement was removed or changed
its text (`scripts/gen-contract --check` is green: 2 dedup, 5 prefix, 1 enterFrame, 1 recover,
1 iface, 14 consumeAt, 317 eqns, 27 g11, 6 pool, 13 g16, 90 deadcell).

Statements whose MEANING moves with their text unchanged, because they name a definition whose
body changed:

- `GoLean.GoCore.Equations.stateWf_empty : StateWf ctx {}` — `StateWf` says more; the empty
  store satisfies it vacuously (proof unchanged).
- `GoLean.GoCore.Equations.storeLoc_root` and `GoLean.GoCore.Equations.bindParams_cons` — each
  takes or states `normalizeValueForTy ctx ty v = .ok v'`, which now also says that the boxes the walk
  meets in `v'` pass the head check. As rewriting rules they are used exactly as before.

Other kept statements name `storeLoc`, `Store.alloc`, `bindParams` or `allocDecls` as opaque
heads (`next_storeK_var`, `allocDecls_cons`, `enterFrame_declared`, the `setup_*` facts, …);
their text and their use are unchanged.

Definitions whose BODY changed, which your `--challenge-from-export` run against your pin will
name: `normalizeValueForTyTy`, `isNormalForTyTy` (the interface arms), `normalizeValueForTy`,
`isNormalForTy`, `writeAt` (the leaf arm) — hence everything built on them: `Store.alloc`,
`storeLoc`, `HeapCell.normal`, `Heap.normalB`, `HeapNormal`, `StateWf`, `MachineWf`, `MultiWf`,
`StmtOpPres`, `snapshotEntriesSelfNormalized`, and the machine arms that normalize or store.
New definitions: `boxHeadTy`, `boxHeadAt`, `boxHeadNormal`, `GoValue.boxesNormal`, `boxesNormalList`,
`boxesNormalFields`, `boxesGuard`. Take a fresh export at or after the landing commit; the route
is the one in the 2026-10-26 note.

## Your lookup proofs and this pin

You told us that about 45 of your lookup proofs locate rows of the whole-program tables by
position, so a re-pin that shifts rows costs you a regeneration. THIS change shifts no table
row: the frontend and the wire are untouched, and the raft twin wire pin
(`scripts/check-frontend-pins`, `baselines/pins/twin-chdriver.wire.json`) is byte-identical at
the lane's tip. What the re-pin does cost you is the unfolding step described under the first
design point, and the body changes the export comparison names. We will say in each reply
whether a change moves that pin.

## Not done, and why

- **Map-payload entries and channel buffers.** Keys, values and elements are normalized through
  `normalizeValueForTy` when they are inserted, so their boxes pass the guard at that moment,
  but `HeapCell.normal` states only the stamp clause for a map payload and nothing for a channel
  payload — as before G23, and for every type, not only interfaces.
- **A function value's captures** are not walked (the type-directed check does not look there
  either: captures are the addresses of the captured variables).
- **Below a payload's head**: a boxed struct's fields, a boxed array's elements and any box
  inside a payload are not checked (the one-level rule, above; the deep form was built and
  withdrawn for its store-time cost).
- **A box at an opaque dynamic type**: its payload is unchecked (above).
- **Repairing a box with the wrong head** instead of refusing it (above).

## Open on our side

Nothing carried from the earlier lists: the `.interface` arm is closed here, and at your word
the Bool checker for `TablesKeyed`/`SliceClosed` (G16) and the `stepFn`-level `StateWf`
preservation theorem are dropped from our open list (your per-arm route stands).
