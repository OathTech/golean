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

## A4 — `Expr.global gid` replaces `Expr.locLit`

**What changed.** `Expr.locLit (l : Loc)` → `Expr.global (gid : Nat)`
(Syntax.lean). The decoder's `"globaladdr"` arm emits `.global gid` (its
`gid < nGlobals` bound check unchanged); `stepFn` evaluates `.global gid`
to `.retV (.addr (.base ⟨gid⟩))` when `gid < s.heap.size` and REFUSES
(`.stuck "global … out of range"`) otherwise; the relation's rule is
`Step.evalGlobal` with the premise `gid < s.heap.size`. `Expr.locSup`'s
arm is `0`. The two hand-built eval-test programs use `.global 0`. [AGENT]

**Wire impact: none (verified, pre-series finding).** The wire already
carried `{"expr":"globaladdr","gid":N}`; only the decoder's core node
changed. The twin-wire pin pins the frontend's emitted bytes, which did not
move — no [USER] call was needed.

**Why nicer.** Program text is address-free again: a `Program` is a
constant (no heap address can be spelled in it), and the machine — not the
decoder — is what turns a global index into a cell address, with the bound
where the bound belongs. The bound is the DRIVER's contract (global `i` is
the `i`-th seeded cell); the decoder's check against the declared global
count is the exact check, the machine's `gid < heap.size` is the
wf-preserving net behind it (a `gid` past the heap is a decoder/driver
breach, refused by name; a `gid` between the global count and the heap
size is unreachable through the decoder).

**Preservation.** On every accepted program every `gid` is below the
declared global count, and the driver seeds exactly that many cells first
(`seedGlobals` asserts cell `i` lands at `.base ⟨i⟩`), so at every
evaluation `gid < heap.size` holds and `.global gid` produces exactly the
`.addr (.base ⟨gid⟩)` the old `.locLit (.base ⟨gid⟩)` produced; no stream
is consulted. Exact.

**Proof deltas.** StateWf: `step_preserves_wf_loc` gains an explicit
`evalGlobal` case (the rule's premise IS the produced address's bound —
6 lines); the module header records that `Expr`/`Stmt`/`Func.locSup` are
now identically zero. MachineSound: `fun_cases stepFn` renumbered — the
`.global` arm is two `fun_cases` premises (77 = the refusal, 78 = the
step) where `locLit` was one, so every positional tag ≥ 78 in
`stepFn_sound` and `stepFn_oblivious` moved by +1 (75 tag renames; the
review's recorded fragility — B3's `Cont` algebra is where these go
named), and each proof gains a 5-line `case77` (the refusal arm is a
`throw … = .ok …` contradiction). `SyntaxEqb`'s arm and case renamed. No
lemma deleted or weakened.

**Owed simplification (recorded, not done here).** With `.global` the
program-text carriers `Expr.locSup`/`optExprSup`/`exprListSup`/
`keyedExprListSup`/`Assignee.locSup`/`Stmt.locSup`/`stmtListSup`/
`selectClause*Sup`/`Func.locSup`/`funcListSup` (StateWf.lean:150–290,
~145 lines) are identically zero, and `StateWf`'s "stored function bodies"
clause is vacuous. Deleting them means restating `Cont.locSup` (every arm
that sums a `Stmt.locSup body`/`exprListSup pending`/`targetPlansSup`),
`ExecState.locSup`, and re-threading the ~40 `*_locSup` plan lemmas and the
hundreds of `hbody : Stmt.locSup … ≤ b` hypotheses through StateWf and
MultiWfSound — the same positional re-proof wave B3 pays for `Cont`, so
it is deferred to wave (iii) rather than paid twice (review §3's own
sequencing argument). [AGENT]

**Gate.** `scripts/capped scripts/ci --diff` on the A4 tree: RESULT PASS,
`cases=3284 pass=3085 fail=199`, baseline diff FULL 3284/3284 no
regression, re-pin guard 0 flips, negative 394/394, eval tests 148/148
(`transcripts/gate-a4.txt`); choice-trace delta vs the pre-series
snapshot: 0 on all 19489 lines (`choice-trace/a4-summary.txt`).

## A5 — a `Platform` record, instantiated once

**What changed.** New module `GoLean/GoCore/Platform.lean` (imported by
Value.lean, so it sits below everything): `structure Platform where
intBits wordBytes maxAlign maxAllocBytes chanHeaderBytes : Nat`,
`Platform.intExclusiveUpperBound p := 2^(p.intBits-1)`, `def gcAmd64 :
Platform := ⟨64, 8, 8, 2^48, 112⟩` carrying the R1 and R16 ENVELOPE
STATEMENTS (moved verbatim in substance from `IntKind.bits?`'s and Ops.lean's
docstrings — transfer caveats, probe pointers, the [USER] fidelity
decision 5(b) citation), and `def platform : Platform := gcAmd64` — THE one
instantiation. `IntKind.bitsAt (p : Platform)` is the parametric width
table (`.int/.uint ↦ p.intBits`) and `IntKind.bits? := bitsAt platform`;
`maxAllocBytes`/`chanHeaderBytes`/`intExclusiveUpperBound` (Ops.lean) read
the platform's fields; `tySizeAlignFuel (p : Platform)` computes go/types'
`gcSizes` from `p.wordBytes`/`p.maxAlign` (pointer-shaped types one word,
strings and interfaces two, slices three; the `sync` struct sizes stay
fixed-width constants, which they are on gc), and `tySizeBytes` passes
`platform`. Machine.lean's arms are textually unchanged (they read the
same names). [AGENT]

**Why nicer.** The pins are one named object with one envelope statement
each; "portable semantics" is a record with a second instance, not a
comment: a 32-bit re-envelope (R1 + R16 together, as the inventory
already insists they move together) is `def gc386 : Platform := ⟨32, 4,
4, 2^32 - 1, 64⟩` plus whatever the frontend/negative lane need — no
surgery in the core.

**Recorded scope (a deviation from the review's sketch).** The review
offered two ways to thread the width to `IntKind.normalize`'s call sites
("make `IntKind.int (bits)` carry it at lowering, or thread `Platform`")
and an `ExecState.platform` field. Neither is taken here: the width is
read from the single instantiation. Consequences, stated plainly: (a) the
core's theorems are stated at `platform` (= `gcAmd64`), not `∀ p`;
`tySizeAlignFuel` alone is genuinely parametric; (b) a second instance
still requires a re-pin of every width-sensitive fixture, exactly as
before. Threading a platform through `ExecState` touches every
state-shape lemma (`σ'.types = σ.types ∧ …` conjunctions across
StateWf/MultiWfSound) — the same wave as review B7's `ProgramCtx`/`Store`
split, where the state gains its context record anyway; deferred there.
[AGENT]

**Preservation.** Definitional: at `gcAmd64` every relocated arm computes
the same number (`2 * 8 = 16`, `3 * 8 = 24`, `2^(64-1) = 2^63`, …), and
`IntKind.bits?` is the old table pointwise; no proof needed changing —
zero proof-side edits, the build is the check. Exact.

**Records to update (records commit).** Latitude inventory R1/R16 "pin
lives at" pointers → `Platform.lean` (`gcAmd64`); `docs/spec-sources.md`
if it names `IntKind.bits?`.

**Gate.** `scripts/capped scripts/ci --diff` on the A5 tree: RESULT PASS,
`cases=3284 pass=3085 fail=199`, baseline diff FULL 3284/3284 no
regression, re-pin guard 0 flips, negative 394/394, eval tests 148/148
(`transcripts/gate-a5.txt`); choice-trace delta vs the pre-series
snapshot: 0 on all 19489 lines (`choice-trace/a5-summary.txt`).

## A6 — `ShadowKey` instead of phantom `Loc`s in the detector

**What changed** (Race.lean; two call sites in Multi.lean; the dedup hash).
`inductive ShadowKey | data (l : Loc) | syncWord (l : Loc) (kind : SyncKind)
(word : SyncWordName) | chanObj (l : Loc)`, with `SyncWordName := state |
sema | w | readerCount | done | m` (an enum, not a `String`), and ONE table
`ShadowKey.overlap` (data/data by `locOverlap`; word/word by identity;
data/word iff the data path is a prefix of the primitive's path, both
orientations; chanObj/chanObj exactly; every mixed pair else `false`).
`RaceState.shadow : List (ShadowKey × ShadowCell)`; the separate
`RaceState.chanObj` shadow is DELETED — `chanObjAccess` is
`accessKey t kind (.chanObj loc)` and `access` is `accessKey t kind (.data
loc)` over one check-then-record function. `syncWord loc kind word` now
builds the key constructor (was `.field loc ⟨"sync." ++ kind.name⟩ word`,
a phantom path under a made-up `TypeId`); `syncEntryKinds`/
`syncReleaseTailKinds` return `List (AccessKind × ShadowKey)` and are
recorded through `RaceState.accessKeys`. `assocSet` is generic in its key
type. The data FOOTPRINT (`RaceAccess := AccessKind × Loc`, every
`stepAccesses`/`stmtOpAccesses`/… producer) is unchanged: those ARE
memory paths — which is the point (`Loc` means "memory path" and only
that). The dedup node hash (`EnumDedup.lean`) loses its separate
`chanObj` fold (the cells now sit in the one shadow fold) — a bucketing
function, no semantic content; the certified records pin observation sets
and the WIRE hash, not node hashes. [AGENT]

**Recorded deviation from the review's sketch.** The review had
`RaceAccess := AccessKind × ShadowKey` throughout. Kept as `AccessKind ×
Loc` for the footprint: every footprint producer names a real memory path,
and wrapping ~30 constructions in `.data` would buy nothing the type
already says; the key type appears exactly where keying is decided (the
shadow and the two sync-word producers). [AGENT]

**Why nicer.** `Loc` means one thing. The two former keying disciplines
(path overlap for data, exact match for channel objects, and the
phantom-path trick for sync words) are three arms of one total table over
an enum-carrying key — the union rule in the sync section's docstring is
now literally `ShadowKey.overlap`. `SyncWordName` makes a misspelled word
a compile error where it was a silently-disjoint string.

**Preservation (verdict-for-verdict).** The conflict test is a pure
function of (kind, key, clock); the keys are in bijection with the old
encodings (`data l ↔ l`; `syncWord l k w ↔ .field l ⟨"sync."++k.name⟩
w.name`; `chanObj l ↔ l` in the second shadow), and `overlap` agrees with
the old tests on every pair that can arise: data/data is `locOverlap`
verbatim; chanObj pairs were exact-match in their own shadow and are
exact-match here, disjoint from everything else exactly as a separate
shadow was; word/word — the old `locOverlap` on two phantom paths holds
iff they are equal (a phantom `.field m ⟨"sync.K"⟩ w` can be a PROPER
prefix of the other only by being a prefix of a real primitive path `m'`,
which no phantom is), i.e. `l = l' ∧ k = k' ∧ w = w'` (the type-id string
is injective in the kind); data/word — the old `locOverlap d (.field m
⟨"sync.K"⟩ w) = (d == .field m … || locPrefix d m) || locPrefix (.field m
…) d`, and the two phantom-equality disjuncts are false on every REAL
path `d`: a program cannot produce a `Loc.field` step whose `TypeId` is
`sync.<Kind>` (the frontend lowers `sync.Mutex` and friends to `Ty.sync`,
whose values are `syncData`, and refuses field access into them), so the
old test reduced to `locPrefix d m` — the new table's arm. That
"phantom paths never coincide with real paths" premise was the OLD
model's unstated soundness assumption; A6 makes it a non-issue by type.
The differential (incl. the `race/` corpus and the `-race` oracle rows)
and the trace are the regression; the per-row set records of the racy
lane are unchanged (zero drift).

**Proof deltas.** None: no proof mentions the shadow's key type
(`RaceState` is decided flat — `deriving instance DecidableEq for
RaceState` now derives through `ShadowKey`, MachineEqb unchanged).

**The first gate was RED — diagnosed and fixed inside the item; both
transcripts kept.** `ci --diff` on the first A6 tree reported
`3083/201`: two `confluent`-lane rows, `goroutines/pipeline/buffered-stage`
and `goroutines/pipeline/two-stage`, went PASS→FAIL with `dedup work
budget exceeded` (`transcripts/gate-a6-red-first-attempt.txt`), while
every other row and the whole choice-trace were unchanged. Not a machine
change: the dedup ENGINE (untrusted tooling) merges states by STRUCTURAL
equality (`RaceState.eqb := decide (a = b)`), and the old channel-object
shadow was a SEPARATE list — so two runs that touched a data key and a
channel key in opposite orders still produced structurally equal
detector states. Folding the two lists into one insertion-ordered list
made those states unequal, merges dropped, and the two channel pipelines
(the corpus's heaviest chan-object/data interleavings) overran their
work caps. Fix: the shadow is CANONICAL — kept sorted by key
(`shadowSet`, over the derived `Ord` on `ShadowKey`/`Loc`/`SyncKind`/
`SyncWordName`), so equal cell sets are structurally equal whatever the
interleaving; this is at least the old merging (old-equal lists have equal
multisets) and strictly more (it also canonicalizes the data/syncWord
interleavings the old single list did not). Sound for the engine's use
(structural equality ⇒ same state) exactly as before; re-run of the two
rows: PASS, 187497 / 866780 nodes (the red attempt hit the cap at
237357 / 951620+). The second full gate is the record below; the incident
is the A-series' one red gate and is reported as such — a change in the
dedup engine's merge RATE, zero change in any observation. Also fixed on
the same pass: the `constructorNameAsVariable` linter warning on the
`overlap` table's `w` binder (the gate treats core warnings as FAIL —
they corrupt the runner's JSON channel).



**Gate.** First attempt RED (`transcripts/gate-a6-red-first-attempt.txt`,
diagnosed above). After the canonical-shadow fix: `scripts/capped
scripts/ci --diff` RESULT PASS, `cases=3284 pass=3085 fail=199`, baseline
diff FULL 3284/3284 no regression (the two pipeline rows PASS again:
187497 / 866780 dedup nodes), re-pin guard 0 flips, negative 394/394,
eval tests 148/148 (`transcripts/gate-a6.txt`). Choice-trace (both
attempts) vs the pre-series snapshot: every consumption column identical
on all 19489 lines; the second attempt's only `obsHash` delta is the same
frontend wire-nondeterminism row as A3's (`choice-trace/a6-summary.txt`).
Machine delta: 0.

## A7 — one accumulator convention and one apply-position accessor: SKIPPED

**Decision [AGENT]: not done in this series; folded into wave (iii).**
Measured footprint before deciding: the apply-position pattern
`.retV v (.stmtOpK|strictK|chanStK|selectOpsK|syncOpK|atomicOpK|rhsK|
tgtOpK …)` appears at ~85 sites across 11 files (Machine 35, MultiSound
11, Multi 9, EnumDedupSound 6, Race 6, ChoiceTrace 5, MultiStreams 5,
CLI 4, MultiWfSound 2, EnumDedupCheck 1, MachineSound 1) — 24 of them
in proofs — and the call-frame accumulator flip touches 12 rule/`stepFn`
sites plus the frame-shape lemmas in StateWf (8), MultiSound (4) and
MultiWfSound (2). Reasons to defer rather than force: (1) the accessor
`Config.applyPos` IS the special case of review B3's `Cont`
classification ("`Cont` classification + generic rebuild + field
bundling"), which wave (iii) builds and re-proves once — doing it here
means paying the positional `fun_cases` re-tagging twice (A4 already
paid one such round: 75 tag renames for one arm); (2) the accumulator
flip changes nothing observable (frames are not values) and its whole
payoff is the downstream bind/plug lemma shape that B3 restates anyway;
(3) the review's own sequencing argument ("they all shift the positional
`fun_cases` tags — pay once") applies. Recorded here so the arc plan's
(iii) picks it up explicitly.


## A8 — dead-generality sweep (done in part; the rest recorded)

**Done.**
- `Stmt.label` → `Stmt.inertLabel` (and `Step.label` → `Step.inertLabel`):
  the name says what the rule does (a no-op marker the frontend never
  emits; `labeled` is the real thing).
- `Stmt.newValue`/`StmtOp.newValue` → `allocNew` (21 token sites; the
  `Option Ty` → `Ty` half of this item landed with A3).
- `TypeDef.unsupported` → `TypeDef.opaqueDecl (reason)`: the frontend's
  BY-DESIGN quarantine of imported/opaque type declarations is no longer
  spelled like `Ty.unsupported`/`Expr.unsupported` (the fail-closed
  frontier). Deviation from the review's `.opaque`: `opaque` is a Lean
  keyword — legal in dotted patterns, illegal as a `cases … with |
  opaque` alternative — so `opaqueDecl`. [AGENT]
- `GoError` → `Stop` (335 token sites across GoLean/ and Tests/, incl.
  `renderGoError` → `renderStop`): the outcome type's name says what it
  is — the way a run STOPS (refusal / terminal / budget), not an error.
- `applyStmtOpCore`'s unused `_nt` parameter dropped (`applyStmtOp` keeps
  `nt` for its rules' arity but binds it `_nt`).
- `Step.stmtOpNullary` DELETED with its `stepFn` dispatch: no `stmtPlan`
  arm emits an empty operand list (every plan starts with its target), so
  the arm was unreachable. The MATCH arm itself must remain for
  exhaustiveness and is now a fail-closed REFUSAL by name
  (`.internal "empty statement operand plan"`, the shape of its sibling
  `some (_, [])` arms) — so the `fun_cases` premise count is unchanged
  (no re-tagging), the refusal arm closes generically in both positional
  proofs, and the two lemmas that existed only for the rule
  (`consumesAppendSlice_execPlan`, `stepFn_exec_plan_nullary`, 27 lines)
  and its three proof cases (`stepFn_sound`'s `case67`,
  `step_complete`'s and `step_complete_any_wf`'s `stmtOpNullary` cases,
  `step_preserves_wf`'s case) are deleted. Preservation: the rule had no
  instance (no plan is empty) — the machine's step relation is unchanged
  on every configuration a program can reach; the interpreter's arm was
  never taken.

**Not done — recorded with reasons.**
- `GoValue.unit`: NOT dead, contrary to the review — `atomicCompute`'s
  `.store` arm produces it as the (never delivered) result of an atomic
  store. Removing it means an `Option GoValue` result on `atomicCompute`
  and restating `applyAtomicOp_wf`'s delivery case; deferred to the B2
  outcome-grammar wave, where the atomic apply's result plumbing is
  reshaped anyway.
- `ExecOutcome.returned/broke/continued`: 60+ sites incl. the
  `execStmtLoop`/`execProgLoop` lemma statements in MachineSound,
  MultiSound (`transferable`), MultiStreams and NPDRF; a medium re-proof
  wave for a type whose three extra constructors are unreachable under a
  root frame. Deferred to (iv) B4 (thread-level `Status`), which retypes
  the outcome anyway.
- `Config.itersNormalized` and its `MachineWf`/`MultiWf` conjunct: 216
  references (StateWf 113, MultiWfSound 103) — vacuous by
  `Cont.itersNormalized_true` but threaded through every wf lemma;
  deleting it is a positional re-proof over both files. Deferred to
  wave (iii) with the `Cont` reshaping.
- `Expr.length/capacity`'s `typ` (constant-fold at the frontend): a
  FRONTEND/wire change (emit.go) — outside this lane's rules (no
  frontend change unless the item is about it). Not done; noted for the
  frontend lane.


**Gate.** `scripts/capped scripts/ci --diff` on the A8 tree: RESULT PASS,
`cases=3284 pass=3085 fail=199`, baseline diff FULL 3284/3284 no
regression, re-pin guard 0 flips, negative 394/394, eval tests 148/148
(`transcripts/gate-a8.txt`); choice-trace delta vs the pre-series
snapshot: 0 on all 19489 lines (`choice-trace/a8-summary.txt`). Net: 20
files, −71 lines (394 added, 465 deleted).
