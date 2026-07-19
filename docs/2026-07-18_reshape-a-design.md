# Reshape A design — heap out of `Config` into Iris `State` (2026-07-18)

Master plan §8 step 2. Makes the relation's `Config` a valid Iris `Expr` (which
may not embed the heap, or `ToVal`'s round-trip law is unsatisfiable — confirmed
by the spike, `docs/2026-07-18_iris-spike-result.md`).

## The minimal correct split

Grounding facts (`State.lean`): local variables are **heap-backed** — `LocalEnv`
maps names → `Loc`, values live in `Heap`. `types`/`functions`/`methods` are the
immutable program. So the whole mutable machine is `ExecState`; the only reason
`Config` can't be an Iris `Expr` is that each constructor **embeds** an
`ExecState` (`Rel.lean:224-231`), i.e. the term carries the heap.

**The fix is to pull that field out, not to restructure `ExecState`:**

- **Iris `Expr` = `Config`**, redefined to carry only the control token +
  continuation (`exec stmt k`, `next k`, `breaking/continuing/returning k`,
  `panicked msg`) — **no `ExecState` field**.
- **Iris `State` = `ExecState`** (unchanged). gen_heap interprets `state.heap`;
  the other components (`locals`, `types`, `functions`, `methods`, `nextAddr`,
  `choices`) ride along in `State`, exactly as HeapLang's `State` carries
  `usedProphId` beside its heap.
- **`Step` becomes `Config → ExecState → Config → ExecState → Prop`** — the state
  is the paired component, not embedded in the term.

### Why this is the right minimal move

- `Ops` (`loadLoc`/`storeLoc`/`lookup`/…) already take a full `ExecState` and are
  **unchanged** — the premises `loadLoc s loc = .ok v`, `storeLoc s … = .ok s'`
  work verbatim, because `s` is now the paired State (still a full `ExecState`).
  No adapter, no `ExecState` reconstruction. The reviewer's "reassemble/re-split"
  tedium (iris B1) disappears because we keep `ExecState` whole as the State.
- `ExecState`, `State.lean`, `Ops.lean`, and the **interpreter (`Eval.lean`) are
  untouched** → the differential suite cannot regress. Blast radius = `Rel.lean`
  + `Correspondence.lean` only.
- `ToVal` round-trip holds trivially: `Val := Unit`, terminal `Config` is
  `.next .stop`, `toVal (.next .stop) = some ()`, `ofVal () = .next .stop`,
  everything else `toVal = none`.

### Decisions taken (recorded)

- **`Val := Unit`, terminal = `.next .stop`.** A GoCore statement run does not
  produce a value; function results are written to caller heap locations, so the
  interesting content is the heap (`State`), reasoned via `pointsTo`. The WP
  postcondition is heap-shaped; `Val` is a marker. (Revisit if a value-returning
  granularity is ever needed.)
- **`panicked` stays a distinct terminal `Config` with no outgoing step**
  (`toVal = none`). Whether Iris treats panic as stuck-safe-failure or a value is
  the panic=stuck-vs-value decision — deferred to the proof port (A2), it does
  not affect the structural reshape.
- **Ambient `types`/`functions`/`methods` stay inside `State` for now.** They are
  immutable; pulling them into a true ambient `ProgEnv` parameter is a later
  cleanliness step, not required for Iris to instantiate. Keeping them in State
  keeps `Ops` premises unchanged this step.
- **`choices` stays in `State` this step; Reshape B removes it.** On the scalar
  subset `consume` never fires, so it is inert here.

## Scope of this step (A1, on Lean 4.29)

Do the split in `Rel.lean` (`Config` → state-free; `Step` on `(Config,
ExecState)` pairs; rewrite every rule to pull `s` into the pair) and update
`Correspondence.lean`'s statements/instances. **Validation: `lake build` green,
the proven correspondence instances re-proved in the new shape, differential
suite untouched.** No iris dependency, no toolchain bump yet — the shape is
already validated by the spike.

## Deferred to A2 (paired with the toolchain bump)

Bump golean 4.29 → 4.31, add iris-lean as a dependency, instantiate the bare
`Language` on the reshaped `Config`/`ExecState` (mirroring `../iris-spike/`), and
port `wp_store`/`wp_load` onto real GoCore. Then Reshape B (oracle out of
`ExecState`) + the first nondeterministic-feature correspondence.
