# The A-series — design note and preservation arguments (2026-09-04)

Status: IN PROGRESS on branch `hygiene-a-series` (design-hygiene arc step
(ii); plan `docs/2026-09-03_design-hygiene-arc.md`; source proposals
`docs/2026-09-03_grumpy-professor-review.md` §3(a) A1–A10). Provenance:
[AGENT] execution inside the [USER]-ratified arc (Mike, 2026-09-03,
relayed by the [AGENT] coordinator, not firsthand: «Great, let's do it as
you propose … our aim is to get the *nicest* faithful go semantics»);
every design choice below is [AGENT] unless marked. Evidence dir:
`docs/evidence/2026-09-03_hygiene-a-series/`. Template: the B1 note
(`docs/2026-09-03_hygiene-b1-stamps-design.md`).

Conventions (review §3): "preserving" = for every program, stream and
fuel the same `Except GoError Result` (constructor, message, readout),
and the choice tape consumed at the same sites with the same bounds in
the same order. Each item below is ONE commit, gated by the full
`scripts/capped scripts/ci --diff` at ZERO baseline drift and by the
whole-corpus labeled-consumption trace (`scripts/choice-trace-corpus`,
6 streams × every executable row) at ZERO consumption delta against the
pre-series snapshot taken at `1b8401c0` (main, both prerequisite lanes
landed). The two prerequisite lanes (`bug087-paniktext` → ChoiceSite
`nilValueMethodText`; `q-trylock` → ChoiceSite `tryLock`) were waited for
per the coordinator's brief; the branch forks from `1b8401c0`.

## Pre-series findings (recorded before the first edit)

- **A4 wire impact: NONE.** The wire already carries
  `{"expr":"globaladdr","gid":N}` (tools/nativefrontend/emit.go
  `globalAddr`); only the DECODER (`GoLean/NativeToIR.lean` `"globaladdr"`
  arm) turns it into a core node. The twin-wire pin
  (`baselines/pins/twin-chdriver.wire.json`, `scripts/check-frontend-pins`)
  pins the frontend's EMITTED bytes, which A4 does not touch. So A4 moves
  no pin and needs no [USER] call; the brief's STOP condition was not
  met.
- **The baseline carries no refusal class or message**
  (`baselines/native-full.tsv` is `result id stage` with stage ∈
  {frontend-export, lean-observation, differential, confluent}), so A9's
  re-tagging of refusal classes is drift-free by construction as long as
  no row's PASS/FAIL result or stage moves; the differential is still run
  as the check.
- `GoValue.unit` is NOT dead (review A8 lists it): `atomicCompute`'s
  `.store` arm returns it as the "no result" value (Machine.lean). A8
  treats it accordingly (see §A8).
- `Expr.length/capacity`'s `typ` constant-folding (A8) is a FRONTEND
  change (emit.go) — outside this lane's rules (no frontend/wire change
  unless the item is about it); SKIPPED, recorded at §A8.

## A1 — the stop grammar as types: `Refusal` / `Terminal` / `GoError`

**What changed** (Value.lean). `GoError` is now
`refusal (r : Refusal) | terminal (t : Terminal) | fuelOut` with
`Refusal := unsupported | stuck | internal` and
`Terminal := panic | fatal | deadlock | raceDetected`. `GoError.status`
and `.message` are per-class projections (`Refusal.status/message`,
`Terminal.status/message`) composed at the top; the status TABLE is
byte-identical to the old flat one (`internal` → `"error"`, `fuelOut` →
`"fuel-out"`, …), so the CLI observation JSON does not move. The review's
`Budget := fuelOut` singleton is kept as the bare constructor
`GoError.fuelOut` (a one-constructor wrapper type would add a level to
every fuel proof for no classification gain; the budget class IS the
constructor). [AGENT]

**The compatibility view.** The seven flat names the machine has always
used (`.panic m`, `.stuck m`, `.unsupported f`, `.internal m`, `.fatal m`,
`.deadlock`, `.raceDetected`) remain valid in BOTH term and pattern
position: they are `@[match_pattern] abbrev`s over the nested type
(`GoError.panic m := .terminal (.panic m)` etc.). So NO `throw` site and
NO `| .error (.panic msg) =>` arm moved (the review estimated "hundreds"
of mechanical edits — this makes them zero; the B2 wave that retires the
panic carrier is where callers move). `simp` sees the view exactly as it
saw constructors through a generated family of 4 injectivity + 42
pairwise-disjointness `@[simp]` lemmas (`GoError.panic_inj`,
`GoError.stuck_ne_panic`, …), and a `cases_stop e` tactic macro
(`rcases e with (_|_|_) | (_|_|_|_) | _`) reproduces the old eight-way
`cases e` shape where a proof enumerated the constructors; `case panic
msg =>` selects by tag suffix as before.

**Why nicer.** "Which stops are Go behaviours" is a type: `Terminal` is
what the differential compares, `Refusal` is what the machine declines,
`fuelOut` is the model's budget. The refusal RULE (A9) has a home
(`Refusal`'s constructor docstrings). Downstream adequacy statements can
quantify `Terminal` instead of "the subset of `GoError` I mean".

**Preservation.** A bijection on constructors (`flat ↔ nested`), the
status/message tables unchanged; every machine definition is unchanged
text whose elaboration goes through the view abbrevs. Exact.

**Proof deltas** (arm for arm): `exceptCong.panic_left` (MachineSound)
splits the nested type explicitly; two `cases e <;> simp_all` sites in
`applySelect`'s wf/normalization proofs (StateWf) split the terminal
class; five `cases e <;> …` sites in MultiSound, one in MultiWfSound,
two in EnumDedupSound go through `cases_stop`. No lemma deleted, none
weakened; two `simp` calls in MachineSound (`applySyncOp_panic_any_ch`,
the empty-picks select arm) gained the view unfoldings.

**Gate.** `scripts/capped scripts/ci --diff` on the A1 tree: RESULT PASS,
`cases=3284 pass=3085 fail=199`, baseline diff FULL 3284/3284 no
regression, re-pin guard 0 flips, negative 394/394
(`docs/evidence/2026-09-03_hygiene-a-series/transcripts/gate-a1.txt`; run
on the uncommitted A1 sources — the tree that became the A1 commit, no
edit between run and commit; the series-final clean-tip gate is in the
records commit). Choice-trace delta vs the pre-series snapshot: see the
evidence README (A1 row).

## A2 — the dense heap: `Heap := Array HeapCell`, addresses are indices

**What changed.** `Heap := Array HeapCell` (State.lean); `Heap.lookup h
(.base ⟨i⟩) = h[i]?` (a field/index path has no cell — paths resolve to
their root first, as before); `ExecState.alloc` is `push` at address
`heap.size`; the `nextAddr` FIELD is deleted and `ExecState.nextAddr σ :=
σ.heap.size` is a derived definition (so it cannot drift from the heap,
and the ~370 proof statements phrased over `σ.nextAddr` stay readable);
`ExecState.freshLoc` and `Heap.set` are deleted. `storeLoc`'s root arm
writes with `Array.set` under the bounds proof the lookup supplies
(`Heap.lookup_lt : Heap.lookup h (.base a) = some c → a.id < h.size`), and
its `none` arm keeps BUG-085's `.internal` refusal — but that refusal is
now the ONLY thing that can happen out of range: the phantom-cell
materialization BUG-085 removed is unrepresentable by type (there is no
`Heap.set`; `Array.set` carries its bound). `StateWf` is unchanged in
statement (`ExecState.locSup σ ≤ σ.nextAddr`) but `Heap.locSup` is now the
sup over cell VALUES only — keys cannot dangle — so half the carriers
leave the invariant; `Heap.lookup_key_locSup` is the array bound
(`Loc.locSup l ≤ h.size`). `EnumDedup`'s state hash keeps both terms
(`nextAddr` and `heap.size`, which were always equal on a dense heap) so
hash values are unchanged; `MachineEqb.ExecState.eqb` drops the redundant
`nextAddr` conjunct and compares the heap as an array
(`eqbArrayP HeapCell.eqb`). [AGENT]

**Recorded deviation from the review's sketch.** The review had
out-of-range `Heap.set` be `stuck`; the arm stays `.internal` — BUG-085's
ruling (an invariant breach, never an ill-shaped program operand), pinned
by the `Tests/GoCoreEval.lean` guard (`storeLoc {} (.base ⟨0⟩) (.int 7)`
must be `.error (.internal _)`), which still passes unchanged. [AGENT]

**Why nicer.** Density is a TYPE fact, not an audited call-graph
invariant (Ops.lean's old 20-line "why the `none` arm is unreachable"
argument is gone; the decoder's `globaladdr` bound and the driver's
`StateWf` assert are defense in depth, not the only defense). The heap
lemmas are array lemmas: `Heap.lookup_locSup` (membership),
`Heap.push_locSup`, `Heap.set_locSup`, `Heap.lookup_push_ne`,
`Heap.lookup_set_ne` — each a few lines over `Array.mem_push` /
`Array.mem_or_eq_of_mem_set` / `Array.getElem?_push` /
`Array.getElem?_set_ne`, replacing the assoc-list inductions.
`Heap.locSup_le_iff : Heap.locSup h ≤ b ↔ ∀ c ∈ h, c.locSup ≤ b` is the
dense address space's whole ownership story (G-REPR's base). NPDRF
obstruction 2 (fresh-cell insertion order — stores that CREATED cells
permuted the assoc list) is DISCHARGED BY CONSTRUCTION: a store can only
overwrite an existing index; only `alloc` creates cells (obstruction 1's
class). Text kept in NPDRF.lean as the record.

**Preservation.** On every machine-reachable state the old
`List (Loc × HeapCell)` had distinct `.base` keys `0 … nextAddr-1`, each
present (density: `alloc` was the only creator and wrote the cell in the
same step; `storeLoc` only overwrote — BUG-085 having removed the append),
so it is in bijection with an `Array HeapCell` of length `nextAddr` under
`key i ↦ index i`; `lookup`, the overwrite, and `alloc` commute with the
bijection, and `nextAddr = size` holds by construction. Every corpus run
starts from the seeded state (`runProgramSetupM`, asserted `StateWf`) and
never leaves the reachable set, so no run observes the representation.
Refusal MESSAGES are byte-identical (the `.internal` text still prints
`repr (Loc.base a)`). The differential is the regression; the trace shows
no consumption moved.

**Proof deltas** (arm for arm). StateWf.lean: `Heap.locSup` via
`heapCellsSup h.toList` (+ `heapCellsSup_eq`, `heapLocSup_eq` restated over
cells, `Heap.locSup_le_iff` NEW); `Heap.lookup_locSup` (3 lines, was a
9-line induction), `Heap.lookup_key_locSup` (restated: `≤ h.size`),
`Heap.set_locSup` (restated over `Array.set`), `Heap.push_locSup` (NEW,
replaces the alloc use of the old `set_locSup`); `storeLoc_shape`'s base
case supplies the bounds proof and `Array.size_set`; `alloc_shape`'s
record bridge is the `push` form. MachineSound.lean: `Heap.lookup_set_ne`
(12-line assoc-list induction) → `Heap.lookup_push_ne` + `Heap.lookup_set_ne`
(array one-liners); `storeLoc_congr`'s base case can no longer `rw` the
lookup (the root match is DEPENDENT — its `Array.set` carries the lookup's
bounds proof), so it splits both lookups and identifies the arms through
the hypothesis (the two mismatched arms are `some = none` contradictions);
the appendSlice spill congruence and `bindIterVars_ok_of_normal`'s three
explicit witness states use the `push` form. NPDRF.lean:
`storeLoc_root_frame` names the lookup hypothesis and passes the bound.
No lemma weakened; `Heap.set` and `ExecState.freshLoc` deleted with their
`simp` mentions (tombstoned here).

**Gate.** `scripts/capped scripts/ci --diff` on the A2 tree: RESULT PASS,
`cases=3284 pass=3085 fail=199`, baseline diff FULL 3284/3284 no
regression, re-pin guard 0 flips, negative 394/394, eval tests 148/148
incl. the BUG-085 guard (`transcripts/gate-a2.txt`). Choice-trace delta vs
the pre-series snapshot: evidence README, A2 row.

## A3 — map/channel payloads out of `GoValue`, into the cell

**What changed.** `HeapCell` is an inductive: `value (declaredTy : Ty)
(v : GoValue) | mapPayload (entries) (nextId) | chanPayload (buf)
(capacity) (closed)` (State.lean); `GoValue.mapData`/`.chanData` are
deleted (Value.lean), with their `eqbFuel` arms, `GoValue.locSup` arms
(StateWf), `StateEqb` soundness cases, and the CLI's two observation-JSON
arms and its `"mapData"` parser arm (neither side of the differential can
emit one; an unknown tag refuses). `declaredTy` is `Ty`, not `Option Ty`:
there are no untyped cells — `Stmt.newValue`/`StmtOp.newValue` carry `typ
: Ty` (the frontend always supplied it; the `Option` was dead generality,
review A8's item, folded in here because A3 needs it), `ExecState.alloc v
ty` allocates a value cell, `ExecState.allocCell c` any cell.
`coerceStoredValue`/`coerceArray`/`coerceStruct` are DELETED: the root
store always normalizes at the declared type; `arraySet` and
`buildArrayValue` no longer coerce per element. Payload access is by
kind: `mapPayload?`/`chanPayload?` read, `storeMapPayload`/
`storeChanPayload` write WHOLE payloads (the only way they were ever
written — Machine.lean's map ops, the chan send/recv/close arms, Multi's
pairing/resume arms, `wakeReady`); `chanCell` is `chanPayload?`;
`mapEntries`, `mapRangeStartSets`, `mapIterLiveEntries`, `len`/`cap`,
`mapGet` read through `mapPayload?`. `loadLoc`/`storeLoc` at a payload
cell REFUSE (`.stuck`, an ill-shaped operand). Every constructor is
enumerated at every match — no `_`-absorbed arm. [AGENT]

**Recorded design choice: ONE root write path.** All three root stores go
through `ExecState.updateCell a f` (State.lean): bounds-checked `Array.set`
under `hi : a.id < heap.size`, `.internal` out of range (BUG-085's ruling
kept), `f` seeing the old cell. Consequences: `updateCell_shape` (StateWf),
`updateCell_lookup_ne` and `updateCell_congr` (MachineSound) are proved
ONCE and `storeLoc_shape`, `storeLoc_root_frame` (NPDRF),
`storeLoc_congr`, `storeMapPayload_pres`, `storeChanPayload_pres` are
corollaries — the dependent-match awkwardness A2's `storeLoc_congr` had
(the `Array.set` proof mentioned the lookup) is gone, because the
dependency is confined to `updateCell`. [AGENT]

**Why nicer.** "A value no expression may produce" is enforced by the
type; `valueEq`/`normalize`/`eqb`/`locSup`/`isNormal` each lose the two
phantom arms; one store discipline (normalize at the declared type — no
second, shape-directed coercion whose agreement with the first had to be
argued); points-to for maps/channels is a distinct cell constructor by
construction (`l ↦ₘ entries`), which is what a channel logic wants.

**Preservation.** (i) Payloads: every payload write was a whole-cell
`storeLoc s l (.mapData …)`/`(.chanData …)` into an UNTYPED cell, where
`coerceStoredValue`'s catch-all `| _, value => return value` was the
identity — exactly `storeMapPayload`/`storeChanPayload`'s effect; every
payload read matched the loaded value's constructor — exactly
`mapPayload?`/`chanPayload?`. The map/chan cells and value cells are
disjoint by allocation (`allocCell` vs `alloc`), so the two paths never
cross on a reachable state. (ii) `coerceStoredValue` on a TYPED root: the
root normalize follows it, and on a well-formed cell they compose to the
root normalize alone — `normalizeValueForTy` at `.int kind` ADOPTS the
incoming kind (`.int (kind.normalize v) kind`), exactly what the coercion's
int arm did against the (already normalized, hence declared-kind) old
element; the float arm's kind check is `normalizeValueForTy`'s own
kind-strict check; array-length / struct-field mismatches refused in both
(message text differs — diagnostics on ill-typed stores, unreachable from
go/types-typed programs). The only untyped value cells were `newValue`s
with `typ = none`, which the frontend never emitted (the two hand-built
eval-test programs that relied on the default now state their types).
Refusal messages at payload sites changed text (`expected map data, got
value …` vs `expected map data, got …`) — diagnostics, unreachable on
accepted programs. The differential and the trace are the regression.

**Proof deltas** (arm for arm; tombstones). DELETED: `coerceStoredValue`,
`coerceArray`, `coerceStruct` (Ops, ~45 lines); `coerceStoredValue_congr`
(MachineSound, 158 lines) and the now-dangling docstring;
`coerceStoredValue_locSup'`/`coerceStoredValue_locSup` (StateWf, ~125
lines); `Heap.lookup_lt` stays (used by nothing but kept as the dense
heap's bound lemma — it is `updateCell`'s `hi` in spirit). NEW:
`ExecState.updateCell_shape`, `mapPayload?_locSup`, `chanPayload?_locSup`,
`storeMapPayload_pres`, `storeChanPayload_pres`, `allocCell_shape`,
`allocCell_wf` (StateWf); `ExecState.updateCell_lookup_ne`,
`ExecState.updateCell_congr` (MachineSound). RESTATED: `HeapCell.locSup`
(three arms), `HeapCell.eqb`/`eqb_sound` (three arms), `alloc_shape`
(`ty : Ty`; a one-line corollary of `allocCell_shape`), `alloc_wf`,
`storeLoc_shape` (base case via `updateCell_shape`, ~12 lines, was ~30),
`storeLoc_congr` (base case 10 lines, was 45), `storeLoc_root_frame` (base
case 2 lines, was 14), `arraySet_locSup`/`arraySet_congr` (no coercion
step), `mapEntries_locSup`, `mapRangeStartSets_locSup`,
`mapIterCandidates_locSup`'s live-entries block, `chanCell_locSup` (one
line), `loadLoc_locSup`'s base arm, `buildArrayValue_locSup`'s loop body,
the `lengthOf`/`capacityOf`/`mapGet` arms of `applyStrictOp_wf`, the ten
channel-store sites in StateWf/MultiWfSound (`storeLoc_pres` →
`storeChanPayload_pres`; the `rw [show GoValue.locSup (.chanData …) = …
from rfl]` bridges vanish), the four map-store sites (`storeLoc_pres` →
`storeMapPayload_pres`), and the makeMap/makeChan cases (`allocCell_wf`/
`allocCell_shape`). MachineSound's `bindIterVars_ok_of_normal` witnesses
use `.value vt value`. Net: 17 files, −277 lines (531 added, 808 deleted).
No lemma weakened.

**Gate.** `scripts/capped scripts/ci --diff` on the A3 tree: RESULT PASS,
`cases=3284 pass=3085 fail=199`, baseline diff FULL 3284/3284 no
regression, re-pin guard 0 flips, negative 394/394, eval tests 148/148
(`transcripts/gate-a3.txt`). Choice-trace vs the pre-series snapshot: every
consumption column identical on all 19489 (id,stream) lines; ONE row's
`obsHash` column moved (`stdlib-source/frontier/index-rune-goto`, an
FR-21 frontier-refusal row, 0 consumptions) — diagnosed in
`choice-trace/a3-summary.txt`: the row's exported WIRE differs between the
two runs (the frontend's quarantine-reason string names whichever `goto`
label its walk meets first — `next` vs `fallback`), and the hash is a
function of the wire alone (main's binary on the before-wire reproduces
the before hash; both binaries agree on the A3 wire). Machine delta: 0.
FINDING, not this lane's to fix (no frontend change in the A-series):
the native frontend's quarantine reason for multi-label goto shapes is
export-nondeterministic; recorded for the stdlib lane (a reviewability
nit — the row's status and its lowering refusal class are stable).
