# Arc 4 / A4-U7 — the field-lens layer + absState v2: design (v1)

Campaign lane `campaign-arc4`, 2026-08-24, [AGENT] throughout (§5
tooling latitude; nothing here changes what any statement means).
The design slice owed by the A4-U6 wave-2 charter item 3
(`docs/campaign-arc4-log.md`), dispatched at U7. Primary sources
read: the Iris reuse survey §5d (campaign branch,
`docs/2026-08-24_campaign-iris-reuse-map.md`); Perennial
`new/golang/theory/mem.v:78-130` (the `Access`/`AccessStrict`
classes, `tac_wp_load`/`tac_wp_store` consuming them); goose
`proofgen/tmpl/types.tmpl:65-77` (the generated per-field
`<T>_access_load_<f>`/`_access_store_<f>` instances); the landed
U5/U6 rename layer (`AllocEq`/`AllocEqWave1`); `AbsState.lean` and
its GAP-V1-1b/-2/-3 registers; MsEquation's per-conjunct cost lesson.

**LINEAGE: Perennial's `Access`/`AccessStrict` field lenses
(O'Hearn-style focusing — "P focuses to A, restoring A' yields P'" —
mechanized as typeclass-searched instances; goose proofgen generates
one load + one store instance per struct field, 76 for raftpb
alone). Our carrier is first-order (Option-readers over `ExecState`,
not iProp points-to), so the pattern ports as: ONE shared reader
combinator + per-field LAW instances discovered by simp-set search —
the search failing IS the footprint-not-covered error, exactly
`mem.v:164`'s behavior. No Iris dependency (survey verdict:
idea-reuse, not import).**

## 1. The problem (what wave 2 needs that v1 does not give)

The message handlers (handleHeartbeat, handleAppendEntries, the
RequestVote pair) read AND write field-granular state on a 33-field
struct (`raft.raft`), the raftLog chain (raftLog → unstable +
storage), and the outboxes (`msgs`/`msgsAfterAppend`). Today:

- `absRaftNode` reads six scalars by hand-written offset-concrete
  chains; every new field means editing the reader and re-deriving
  its `_ren` transport by hand.
- Equation conclusions that touch k fields cost k whole-window
  kernel re-evaluations (the MsEquation lesson: per-conjunct facts,
  348 s for a 246-step handler; the sort-leaf pathology was the same
  shape). A wave-2 handler touching 10+ fields on this pattern is
  a cost cliff.
- absState preservation ("the handler did not touch X") is proved by
  re-projecting whole states, not by a store-miss law.

## 2. The lens layer (general half — new module `GoLeanProofs/Lens.lean`)

First-order carrier. One reader combinator per access shape:

```lean
/-- Field readout at a base cell (fail closed: wrong tag → none). -/
def fieldRead (σ : ExecState) (a : Addr) (tid : TypeId) (f : String) :
    Option GoValue
/-- fieldRead + uint64 decode + wrap collapse: the projection-facing
form. The wrap hypothesis is the U3 `unrm` story, absorbed here. -/
def fieldReadU64 (σ : ExecState) (a : Addr) (tid : TypeId) (f : String) :
    Option Int
/-- Slice readout through a slice-valued field: backing array walk
(offset/len), element decode passed in. Generalizes `absEntsFrom`. -/
def sliceRead (σ : ExecState) (base : GoValue)
    (elem : ExecState → GoValue → Option α) : Option (List α)
```

The LAW FAMILIES (general, proved once over the combinators):

| law | content | consumer |
|---|---|---|
| L1 focus | whole-struct cell fact ⇒ `fieldRead` value | readouts at fixtures |
| L2 store-miss (THE FRAME HALF) | machine store to field g ≠ f at a (the `storeTarget` path, re-normalization included) preserves `fieldReadU64 _ _ _ f` | absState preservation without window re-evaluation |
| L3 store-hit | store of v to f ⇒ `fieldReadU64` reads `normalize v` | post-state readouts |
| L4 rename | `FrameSim r … σ σF` ⇒ `fieldRead σF ⟨r a.id⟩ = (fieldRead σ a).map (renameValue r)`; `fieldReadU64` transports verbatim (scalars loc-free) | the U5/U6 placement layer — ONE lemma covers every lens consumer (no per-reader `_ren` proofs ever again; `absRaftNode_ren`'s hand pattern retires for new readers) |

L2 is the honest cost center and the first kill-point: the machine
re-normalizes the WHOLE struct on a field store
(`normalizeValueForTy` at the declared type — the U3 norm-wrap
finding), so L2 must show per-field preservation across
normalization. The lever exists: normalization is field-pointwise on
structs (`normalizeFieldsWith` walks fields independently), so
store-miss preservation is `StructFields.set`-vs-`lookup`
commutation + per-FIELD normalization stability — the pilot ledger's
parked "normality preservation under StructFields.set" row, now with
its real consumer. If contact shows normalization is NOT
field-pointwise for some wave-2 type (embedded structs, arrays), the
kill-point fires: L2 narrows to the scalar-field fragment and the
non-scalar fields stay on the window-transport path, recorded.

Division of labor (survey's contrast, made binding): **TableExt
computes whole-struct stores INSIDE windows (unchanged, zero edits);
the lens reasons AT window boundaries** — equation conclusions,
absState definitions, preservation arguments. The measurable payoff
target (checked at slice E): one window fact + k lens applications
replaces k whole-window kernel facts; MsEquation-shaped modules drop
from O(k · window) to O(window + k) kernel work.

## 3. Per-field instances (target half — generated `Specs/Raft/LensInst.lean`)

One instance pack per (TypeId, field) of the wave-2-relevant types,
from the PINNED lowering's struct table (`twinLowered.typeDefs`):
`raft.raft` (33), `raft.raftLog`, `raft.unstable`,
`raft.MemoryStorage`, `raftpb.Entry`, `raftpb.Message`,
`tracker.Progress` — ≈ 70–75 field instances. Each pack: the L1
instance at the pinned declared type, the L2/L3 instances with the
field's normalization data (kind, wrap behavior at its declared
type), tagged into one simp set (working name `@[raft_lens]`).
Discharge in equation proofs is `simp only [raft_lens] `/`rw` — the
simp-match is the footprint search; a missing instance fails loudly
at the proof, never silently.

Mechanism call ([AGENT]): SIMP-SET LEMMA FAMILIES, not typeclasses.
Our discharge sites are first-order rewrites (no dependent synthesis
needed); Perennial needs typeclass search because its instances feed
tactics mid-WP. Revisit only if a wave-2 store walk turns out to
need synthesis.

### Hand vs generated — costed, and the recommendation

- HAND: ~2 lemmas × ~75 fields × 3–4 lines ≈ 500+ lines of
  error-prone boilerplate, re-done at every pin move.
- GENERATED: a ~150-line printer probe (the `BfLitGen`/`BcLitGen`
  pattern, third consumer — this folds the U4 promotion-ledger
  "literal-generation printer" row's future into one instrument)
  reading `twinLowered.typeDefs`, emitting `LensInst.lean` with
  every lemma proved by `rfl`/`kernel_rfl`/`decide`.
- **RECOMMENDATION: GENERATED.** The generator is an INSTRUMENT, not
  proof code (dispatch language confirmed): it lives probe-side
  (`artifacts/probe/LensGen.lean`), its output is kernel-checked in
  the default build, and a pin move regenerates + rebuilds — the
  build is the drift alarm, exactly the BfLit trust story.

## 4. absState v2 (the layer-(A) growth, lens-consuming from birth)

- `absRaftLog` (closes GAP-V1-1b): the log view = `absStorageEnts`
  (landed, U4) ⊕ the unstable overlay (`unstable.entries` slice via
  `sliceRead`, `unstable.offset` arithmetic re-grounded from
  `log_unstable.go`). CONTACT RESOLVED at this design (probe
  `LensContactProbe`, this unit): `raftLog.unstable` is an EMBEDDED
  VALUE field (`Ty.defined raft.unstable`, not a pointer) — one cell
  hop plus a VALUE-level projection; the combinator set therefore
  includes `fieldOfValue : GoValue → TypeId → String → Option
  GoValue` for nested struct values (L-laws stated over it too);
  `unstable.entries : slice (*raftpb.Entry)`, `offset : uint64` —
  the `sliceRead ∘ absEntry` + arithmetic plan confirmed.
- `absMessage`: `raftpb.Message` → abstract record. CONTACT
  (same probe): 14 fields — Type/To/From/Term/LogTerm/Index/Commit/
  Vote/RejectHint as plainpb pointer-scalars (`derefU64` pattern),
  `Reject : *bool` (a `derefBool` sibling), `Entries` via
  `sliceRead` ∘ `absEntry`, `Context` a byte slice, and
  **`Responses : slice (*raftpb.Message)` — RECURSIVE**: `absMessage`
  needs fuel or a structural bound. Census item for slice D: whether
  wave-2 handlers read `Responses` at all — if not (expected: it is
  the local-append fast path's plumbing), v2 projects it as a
  deliberate GAP-V2-1 (fail-closed unread field), recorded not
  guessed.
- `absOutbox` (feeds GAP-V1-3): `r.msgs` / `r.msgsAfterAppend` via
  `sliceRead` ∘ `absMessage`. Append-grown backing arrays relocate
  freely under L4 (the base is a value, renamed consistently).
- v1's `absRaftNode` stays VERBATIM (shipped statements untouched);
  v2 readers are additive beside it. New readers state every access
  through the combinators, so L4 gives their placement transport for
  free — symbolic-from-birth (charter item 1) holds by construction.
- GAP-V1-2 (tracker) and -4 (AbstractNet) remain open; -5 stays by
  design (latitude-bearing fields unprojected).

## 5. Slice ladder for U7+ (each with its kill-point)

- **A (this design + core):** `Lens.lean` combinators + L1 + L4 (the
  cheap laws; L4 subsumes the per-reader `_ren` pattern).
- **B:** L2/L3 against the machine's store path. KILL-POINT: if
  normalization is not field-pointwise for a needed type, narrow to
  scalar fields + record; if even scalars fail, stop — the lens
  becomes readout-only (L1/L4) and preservation stays on windows.
- **C:** the generator + `LensInst.lean` (≈75 instances, kernel-
  checked). KILL-POINT: generated-file build time; if kernel cost of
  75 rfl-instances exceeds ~2 min, split per-type modules (the
  BfSortLeaf precedent, retired by literalization — same fix shape).
- **D:** absState v2 readers + probes (unstable layout contact
  first).
- **E:** handleHeartbeat symbolic-from-birth on the new machinery,
  fixture born re-sited (charter items 1–2), witness included; the
  slice that MEASURES the lens's cost claim against the MsEquation
  baseline.

## 6. Boundaries (restated as binding)

- Sym stays outside every statement closure; the lens layer is proof
  infrastructure, `Lens.lean` imports machine vocabulary only (no
  Sym, no Specs — the general/target lint applies).
- Shipped statements (v1 readers, the five concrete equations, the
  U5/U6 alloc forms) stay verbatim; everything here is additive.
- The generator never becomes load-bearing cleverness: it emits
  kernel-checked source; deleting it loses regeneration convenience,
  never soundness (the clever-tricks scaffold rule).
- Fixture re-siting (U6 charter item 2's consolidation) is a
  SEPARATE unit — this design does not depend on it, but slice E's
  new fixture is born re-sited.
