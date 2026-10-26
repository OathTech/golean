# Reply to raft-proofs' ask G22: `StateWf` states the map-payload stamp clause

2026-10-27, [AGENT] lane `core/g22-map-stamps-1026` for GoLean, answering
`raft-proofs/docs/2026-10-26_golean-ask-map-stamps.md` (G22, at your `bad919b0` pin; relayed
by the [USER] 2026-10-26). The pin to consume: GoLean `main` at
`<the landing commit — the coordinator fills this in>` or later (toolchain
`leanprover/lean4:v4.35.0`); this lane is stacked on G21's
(`docs/2026-10-27_reply-to-raft-proofs-g21.md`), so one pin takes both. Earlier replies:
`docs/2026-10-21_reply-to-raft-proofs.md` (G9–G11),
`docs/2026-10-23_reply-to-raft-proofs-g16-g18.md` (G16, G18),
`docs/2026-10-26_note-to-raft-proofs.md` (G19, BUG-131, BUG-132). G22 is done: the clause is
stated, preserved through the per-op family and pinned; no behaviour changed (no row of the
differential corpus changed its answer); no comparator-contract statement changed its text,
and exactly one strengthens in meaning (§ The contract).

## The clause, as stated

`GoLean/GoCore/Ops.lean`, beside `HeapCell.normal`:

```lean
/-- The entry stamps of a map payload, in entry order. -/
def mapStamps (entries : Array (Nat × GoValue × GoValue)) : List Nat :=
  entries.toList.map (·.1)

/-- Distinctness of a stamp list — a structural `Bool`, kernel-reducible. -/
def stampsDistinct : List Nat → Bool
  | [] => true
  | x :: xs => !xs.contains x && stampsDistinct xs

/-- THE MAP-PAYLOAD INVARIANT: the stamps are distinct and every one is below `nextId`. -/
def mapPayloadWf (entries : Array (Nat × GoValue × GoValue)) (nextId : Nat) : Bool :=
  stampsDistinct (mapStamps entries) && (mapStamps entries).all (· < nextId)

def HeapCell.normal (types : TypeEnv) : HeapCell → Bool
  | .value ty v => isNormalForTy types ty v
  | .mapPayload entries nextId => mapPayloadWf entries nextId   -- was `true`
  | .chanPayload .. => true
```

`StateWf ctx σ` is still `Store.locSup σ ≤ σ.nextAddr ∧ HeapNormal ctx σ`, and `HeapNormal`
is still `Heap.normalB ctx.types σ.heap = true` (`σ.heap.toList.all (HeapCell.normal
ctx.types)`): the clause entered through the `.mapPayload` arm. Its Prop reading, which is
the form you asked for:

```lean
theorem mapPayloadWf_iff :
    mapPayloadWf es n = true ↔ (mapStamps es).Nodup ∧ ∀ id ∈ mapStamps es, id < n
theorem StateWf.mapPayload_of (h : StateWf ctx σ)
    (hl : Heap.lookup σ.heap l = some (.mapPayload es n)) :
    (mapStamps es).Nodup ∧ ∀ id ∈ mapStamps es, id < n
```

(`HeapNormal.mapPayload_of` is the same off `HeapNormal`; `stampsDistinct_iff` bridges the
Bool to `List.Nodup`.) `StateWf` stays decidable and kernel-reducible on a concrete store —
`stampsDistinct` is a plain structural `Bool` like the other checkers, so `decide` never meets
an instance; the setup path's runtime assert (`if StateWf pctx s₀`) compiles the same Bool.

**Why `HeapNormal`, not a third conjunct of `StateWf`** ([AGENT], 2026-10-27; one definition
to move if you or the owner prefer the other shape): the file's structure. `HeapNormal` is the
per-cell conjunct — a structural `all` over the heap — and every heap write is already proved
through `HeapNormal.of_updateCell` / `of_allocCell`, which carry ONE obligation per written
cell. A per-cell clause slots in there with no change to any value-cell proof (`storeLoc`,
`Store.alloc`, the channel writer: their cell functions never produce a map payload, so their
obligations close as before) and the burden lands on the payload writers alone. A third
conjunct would have re-plumbed `StateWf.mk'` and every one of its users for the same content,
plus a «payloads untouched» transport lemma for every non-map write. The one cost is naming:
`HeapCell.normal` now reads «a value cell self-normalized at its type, a map payload
well-stamped»; its docstring and `HeapNormal`'s say so.

## Preservation

Where the premise comes from, and where it is discharged (`GoLean/GoCore/StateWf.lean`,
section «The map-payload clause»):

| step | theorem | the stamp fact used |
|---|---|---|
| the peek (every payload edit starts from it) | `mapEntries_wf`, `mapPayload?_wf` (off `HeapNormal`) | the OLD payload is well-stamped |
| the write | `HeapNormal.of_storeMapPayload`, `storeMapPayload_pres` — each gained the premise `hwf : mapPayloadWf entries nextId = true` for the NEW payload (both internal; neither is in the contract) | |
| `mapAssign`, present key | `mapAssignValue_pres` → `mapPayloadWf_set!` | `mapStamps_set!_same`: the entry keeps its stamp, so the stamp list is unchanged |
| `mapAssign`, absent key | `mapAssignValue_pres` → `mapPayloadWf_push` | `mapStamps_push`: the new stamp is the counter, which every old stamp is below; the counter advances |
| `mapDelete`, present key | `applyStmtOpCore_wf` → `mapPayloadWf_eraseIdx!` | a sublist of distinct stamps, the counter kept (`eraseIdx!` in range or not) |
| `mapDelete`, absent key | `applyStmtOpCore_wf` → the peeked payload's own clause | the payload is rewritten unchanged (the emitted write) |
| `clearMap` | `applyStmtOpCore_wf` → `mapPayloadWf_empty` | `#[]` at any counter |
| `makeMap` | `applyStmtOpCore_wf` → `allocCell_wf` | the birth cell `mapPayload #[] 0` meets the normality premise by `rfl`, as before |
| `storeTarget`'s map-element arm, `unseq`'s stores | through `mapAssignValue_pres` | unchanged |

Every other arm touches no payload, and no proof of it changed: the value-cell writes close
their per-cell obligation exactly as before. The seeded store: `seedCells_wf` is unchanged —
the loader allocates value cells only (`Store.alloc`; a seeded map is the nil map value, a
VALUE cell at map type, about which the clause says nothing); a map payload is born only by
`makeMap`. The statements of `applyStrictOp_wf`, `storeTarget_pres`, `unseqLoad_pres` and the
G16 `_mono`/`_eq` lemmas are untouched, and so are their proofs: the only repairs were the two
premises above and the five call sites that discharge them.

For your range rule, two more, since that is what the ask is for:

```lean
theorem mapIterLiveEntries_nodup (hn : HeapNormal ctx σ)
    (h : mapIterLiveEntries σ base = .ok (es, tr)) : (mapStamps es).Nodup
theorem mapIterCandidates_nodup (hn : HeapNormal ctx σ)
    (h : mapIterCandidates ctx σ keyTy valTy base produced = .ok (cands, tr)) :
    (mapStamps cands).Nodup
```

— the pick-time candidates of a range, off a normal heap, carry distinct stamps:
`filterCandidateList` is a `List.filter` on stamps, so it drops exactly the produced entries
and never a second entry under a repeated stamp.

## The contract

No statement of `comparator.json` changed its text (385 statements; `scripts/gen-contract
--check` green with no regeneration). Statements whose MEANING strengthens, because they name
`StateWf` and `StateWf` now says more: exactly one —

- `GoLean.GoCore.Equations.stateWf_empty : ∀ {ctx : ProgramCtx}, StateWf ctx {}` — the empty
  store satisfies the clause vacuously (its proof is unchanged).

No other kept statement names `StateWf`, `HeapNormal` or `HeapCell.normal`, and none takes
`StateWf` as a premise (the `Prefix`/`Finish` laws are stated under `NoRefusal` alone;
`classification_wf` is a `_stmt` definition in `ExecutionStatement.lean`, outside the
contract, whose proof never used the invariant). Definitions whose BODY changed, which your
`--challenge-from-export` run against `bad919b0` will name: `HeapCell.normal` (hence
`Heap.normalB`, `HeapNormal`, `StateWf`, `MachineWf`, `MultiWf`, `StmtOpPres`); new:
`mapStamps`, `stampsDistinct`, `mapPayloadWf`. Take a fresh export at or after the landing
commit; the route is the one in the 2026-10-26 note.

## Pins

`Tests/GoCoreContract.lean` §A, kernel-decided on small stores, in the core audit's name list:
`repeated_stamp_refused` (stamps `0, 0` at counter 2 — the shape of your
`repeated_stamp_skips` — is `¬ StateWf`), `stamp_at_counter_refused` (stamps `0, 2` at counter
2), `distinct_stamps_admitted` (a map value cell pointing at a payload with stamps `0, 3` at
counter 4 — a gap, since a deleted stamp is never reused — is `StateWf`).
`Tests/GoCoreEval.lean` `g22MapStampTests`: the same three shapes and a stamp past the counter
through `HeapNormal`/`StateWf`/`mapPayloadWf` at runtime, and the machine's own payload — born
by `allocCell (.mapPayload #[] 0)` (the `makeMap` arm's cell), then `mapAssignValue` ×3
(stamps `0, 1, 2`, counter 3), a replace at a present key (unchanged), `mapDelete` of key 2
(stamps `0, 2`, counter 3), the re-insert of that key (stamps `0, 2, 3`, counter 4: fresh,
never the old stamp), an absent-key `mapDelete` (unchanged), `clearMap` (`[]`, counter 4) and
an insert after it (stamp `4`, counter 5) — `StateWf` after every edit, with exactly those
stamps and counters read back through `mapPayload?`/`mapStamps`.

## Not done, and why

- **The `stepFn`-level `StateWf` preservation theorem**: still not started (as the G21 reply
  says); your per-arm fallback stands, and the per-op family it rests on now carries the
  clause.
- **A frame-level statement about an in-flight range** (`Cont.mapIterK`'s `produced` array
  against the live stamps): not in the ask; say if the range rule needs one.
- **The channel payload**: no clause (it carries no stamps; its buffer is bounded by the
  address clause).
- **`Sym.HeapTyped`**: nothing on our side — the clause you carried there (DL-302) is now
  `StateWf`'s, so it can retire at the pin.

## Open on our side

- The `.interface` arm of the normal form (G21): on request.
- The Bool checker for `TablesKeyed`/`SliceClosed` (G16): on request.
