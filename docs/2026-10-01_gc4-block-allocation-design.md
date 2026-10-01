# G-C4 design note — block-entry allocation (window row 6, C4)

STATUS: RULED 2026-10-01 — G-C4 PASSED with all nine §7 decisions as recommended ([USER] Mike, verbatim, relayed by the [AGENT]
coordinator — cite as relayed: «Those costs seem fine to me. Go ahead with these decisions. You can work on block allocation on the
basis of approving all of your recommendations.»; ledger record `docs/2026-08-31_qrow-rulings.md` «G-C4 (block-entry allocation)
passed — RULED (2026-10-01)»; landing lane `core/block-allocation-1001`, handoff `docs/2026-10-01_block-allocation-handoff.md`).
Was: PROPOSED — HARD-STOP design gate; the [USER] passes or amends §7. [AGENT] design writer, 2026-10-01, branch `docs/gc4-design-1001`
off `main` @ `ac6baa31` (P, C3, B6 landed; the `Intn` pick site 5b still to run — nothing below depends on it). Inputs:
`docs/2026-09-03_design-hygiene-arc.md` (v) (G-C4 RULED in principle [USER] 2026-09-04, relayed, with the «up to heap isomorphism» caveat);
`docs/2026-09-04_reasoning-surface-plan.md` §3.C4; charter row 6 + decision 9 (RULED 2026-09-24: the SCOPED form, behavioural gate
unchanged); `docs/2026-09-23_response-from-logic-team.md` §4 C4; `docs/2026-09-28_note-from-logic-team.md` request 4;
`docs/2026-09-30_numeric-locals-handoff.md` §5. Code cited at `ac6baa31`; two `go run` probes against go1.26.5 (scratch deleted; outputs in §2).

## 1. What changes and why

**Today — two allocation disciplines for one concept** (plan G9). `Stmt.block decls ss` (Syntax.lean:599) allocates `decls` at block entry via
`allocDecls ctx env.pushScope` (`Step.block`, Machine.lean:5939; StepFn.lean:414) — but the decoder ALWAYS emits `.block #[] stmts`
(NativeToIR.lean:1685 and its synthetic if/for/range blocks :2999–3056, :2203–2313) and lowers every declaration as an inline
`Stmt.initialization p` (Syntax.lean:608) at its source point — `declaresOf` :937, `decodeVar` :2978, the `$`-temps (`$cr{i}`, `$ta`, `$ret{i}`,
`$blank{i}`, `$lit`, `$rcoll`…, `$forFirst` :3051), the lifted `select` targets :1955ff — a step that REWRITES the enclosing `.seq` frame's environment
(`Step.initialization`, Machine.lean:5942: `.seq rest env k ↦ .seq rest (env.declare p.id loc) k`; `stepFn` throws `.internal` under a
foreign-env sequence and `stuck` elsewhere, StepFn.lean:417–425), so a `Frame.seq`'s `env` is not fixed across its own statements and every
sequencing law a client states carries «no declaration in between». The B6 slot lemmas (`allocDecls_lookup`, Machine.lean:6912;
`enterFrame_lookup_arg/_result` :6990/:7003) already state the entry layout `s.heap.size + i`.

**After C4.** The decoder threads a per-block declaration list: every site that emitted `.initialization p` records `p` on the block it is
lowering under, and each block (wire `block`; the decoder's synthetic if/for/range/loop-body blocks) closes as `.block decls stmts`; the
initializer stays where it was, as the `.assign` it already is (`x := e` is today `.initialization x; x = e`, so «storage allocation separate
from initializer execution» holds by construction — calls, reads, failures and binding visibility at the source point are untouched).
`Stmt.initialization`, `Step.initialization`, the `stepFn` arm and its two refusal texts are DELETED; `allocDecls` stays (it IS the block-entry
allocator); `bindParams`/`enterFrame` are untouched. **Gain for the logic team:** `Frame.seq rest env` is fixed from creation to pop —
`.next (.seq (s :: rest) env k) ↦ .exec s env (.seq rest env k)` and, after `s`, `.next (.seq rest env k)` with the SAME `env`, for every `s`:
frame-local environment laws, a sequential bind with no declaration side condition. Why entry allocation is unobservable: a local's scope
begins at the END of its declaration (spec#Declarations_and_scope), so nothing reads the cell before its `.assign`; freshness per iteration is spec#For_statements.

## 2. The address-sensitive-escape audit (the ruled precondition)

Addresses are heap indices: `Store.allocCell` puts a cell at `heap.size` (Store.lean:35), so allocation ORDER is the address. C4 moves a
block's allocations earlier (to entry) and in declaration order; cells for declarations an early `return`/`break`/`continue` would have
skipped now exist (the «extra private cells»). Verdict per channel — in sum: NO currently-supported observation changes; channel 5 is a
schema limit predating C4, channel 10 the one place a row can move (via a budget):

| # | Channel | Today | Verdict |
|---|---|---|---|
| 1 | Program output via `fmt`: `%p`; `%d`/`%x` on a pointer (gc formats the address) | `parseFmtFormat`'s verb set has no `p`; the kind matrix admits `%d` on basic integer kinds only and has no pointer/chan/map/func row — anything outside refuses naming the pair (fmtdesugar.go:20–60, :1150–1215); `Println` is not modeled (emit.go:1083, :1354) | UNAFFECTED (refused by name) |
| 2 | `uintptr(unsafe.Pointer(p))`, `reflect` `.Pointer()`/`UnsafeAddr` | `unsafe` refused/quarantined (emit.go:45–66, H-3); `uintptr` lowers to `uint64` (NativeToIR.lean:347) and the harness refuses the kind (coverageharness/main.go:520); no reflect facility exposes addresses | UNAFFECTED |
| 3 | Pointer equality, aliasing, `==` on reference kinds | `Loc` equality, renamed uniformly by any injection | PRESERVED (the claim in §3) |
| 4 | Map iteration over pointer keys | iteration is by entry-identity STAMP, not address (State.lean:40–50; Ops.lean:3275) | UNAFFECTED |
| 5 | The readout JSON `values` (`coverage-observations`) | `locJson` renders the RAW id for `.addr`, slice/map/chan bases (CLI.lean:88, :156, :188–215). **Finding:** the plan's «the observation JSON does not record a `Loc`» was wrong. BUT the Go harness refuses Pointer/Slice/Map/Chan/Func readout kinds («unsupported Go observation kind», main.go:497–592), so no PASS row can carry one; the certified set has 0 `addr` tokens; the 10 `go-observation` rows are status-class | AFFECTED in principle, EXCLUDED from the comparable surface today — posed as decision 6, not absorbed |
| 6 | Refusal/`internal` texts with `repr (Loc.base a)` | Store.lean:61; Ops.lean:1827–1832 — invariant-breach paths a decoded program never reaches; the B6 unbound-variable text prints the `VarId` | UNAFFECTED |
| 7 | Race detector keys / NPDRF / detector-soundness matrix | `ShadowKey` over `Loc` (Race.lean:303–324); verdicts compared, never addresses; overlap is renaming-invariant | UNAFFECTED (renamed uniformly) |
| 8 | Dedup engine (`EnumDedup`, `dedupNodeEqb`) and the certified slow-tier row | the node hash salts `heap.size`/`nextAddr` (EnumDedup.lean:105–113) and equality is whole-state; earlier cells change which interleavings merge (the A6 precedent: merge rate, no observation); the claim is `argv + wire_sha256` + `observations_sha256`; work cap 60 M, r57 wall 121 s | observations UNCHANGED expected; node/edge counts MAY move; a work-cap exceedance is a visible refusal |
| 9 | `repr` pins in tests | hand-built states only (GoCoreContract.lean:98–370, GoCoreEval.lean:2344–2461); no test pins a program-derived heap | UNAFFECTED; the 7 hand-built `.initialization` uses are rewritten |
| 10 | Fuel | each declaration was ONE `stepFn` step; block entry is one step for all of them → fewer steps per block | AFFECTED: budget rows (`arrays/materialization-budget/over-budget` FAIL; `noodler/budget/*` PASS) may move — invariant-2 STOP-and-report, decision 7 |
| 11 | Per-iteration loop variables, backward `goto` (the plan's two probe classes) | body-locals live in the loop-body `.block` (decodeFor :3036; range `iter` blocks; `emitForPerIteration` emit.go:4296–4380 declares the copy INSIDE the body) — fresh per entry, as now; `goto` hoists refuse captured/address-taken variables (emit.go:2735–2760) | UNAFFECTED; gc witnesses: probe p1 (body-local `&x` per iteration, closures, a `continue` before a declaration) `false false 0 10 20 / 0 10 20 / 4 1`; probe p2 (backward `goto` over `x := n; &x`) `false false 0 1 2` |

## 3. The preservation claim (scoped form, charter decision 9)

For a decoded program `P` and its C4 lowering `P'`: an INJECTION `ρ` from the old heap's addresses into the new heap's (order-preserving within
one block's declarations) such that every old run has a new run whose per-step labels agree under `ρ` (`trace` renamed; `picks` and `out`
EQUAL), with STUTTERING only at the deleted `.initialization` steps (one old step ↦ none) and at block entry (one step ↦ one step allocating
`n` cells), and the new heap = `ρ`(old heap) + PRIVATE cells — not-yet-reached or skipped declarations at their zero value, named by no value,
label or environment entry except the owning `.seq`'s. Observable domain: `out`, the terminal classification and abort text, the choice
consumption bound-for-bound, the readout JSON modulo channel 5's ids, race/DRF verdicts; pointer equality and aliasing hold because `ρ` is
injective. PROVED in the lane: the D8 lemmas; the existing coherence (`stepFn_sound`/`step_complete`, packet A/B) re-established AS STATED.
DIFFERENTIALLY CHECKED, not proved: the run correspondence itself — `ci --diff` at zero drift, the whole-corpus choice trace byte-identical per
consumption, the detector-soundness matrix cell-for-cell. The run-level simulation is NOT claimed as a theorem (C5's honesty on fuel).

## 4. The semantics decisions C4 forces

- **D1 (GENUINE) — the allocation unit.** (a) the innermost enclosing `.block`, at entry [REC]; (b) the declaration site (= today); (c) the
  function body. (a) is Go's block rule (spec#Blocks); (c) breaks per-iteration freshness. The decoder ENFORCES (fail closed) that every
  loop body is a `.block` (decodeFor/range already wrap; `breakable` bodies arrive as wire blocks, emit.go:5049/:5316): fresh cells per entry.
- **D2 (GENUINE) — the wire.** W1: schema `golean-native-v3` UNCHANGED; the decoder hoists (it already walks every block's declarations
  scope-exactly for R1, NativeToIR.lean:1676–1684) [REC]. W2: the frontend emits block `decls` (schema v4; twin and certified `wire_sha256`
  move; `--slow` on the lane). W1 keeps the `declare` at the source point on the wire (the binding-visibility record the logic team asked to
  keep) and confines the blast radius to `GoLean/`.
- **D3 (GENUINE) — the `unseq` binder cells.** `unseqEnter` (Machine.lean:6581; `stepUnseqEnter` StepFn.lean:205) uses the same in-place
  idiom (`.seq rest env' k`) so that `thenB`'s declarations survive; with C4 those are hoisted to the block, so the reason lapses. (a) keep the
  in-place extension — one exception to the fixed-env law; (b) allocate the cells at ENTER into a sweep-PRIVATE scope (`env.pushScope`), the
  continuation stays `.seq rest env k` [REC]; (c) hoist the cells to the block too (`unseqEntryCheck?` Machine.lean:2101 inverts; a larger
  UnseqSound re-proof). (b) changes one rule's continuation, keeps the B6 F3 check as is, and makes the cells provably sweep-private.
- **D4 (ROUTINE, corrects the ruled text) — `seqCont` stays as is** (Machine.lean:3949; BridgeSet rows 98–100). The plan's «splice
  unconditionally; with fixed envs both choices are equivalent» is WRONG when `env' ≠ env` (`rest` would run under the wrong env); with fixed
  envs that branch is unreachable for decoded programs, and the test is kept for totality.
- **D5 (ROUTINE) — same-spelling decoder temporaries** (`tmp` interns per function, NativeToIR.lean:103): one cell per id per block entry (the
  block's list deduped; `namesDistinct` is the layout lemma's premise, as in `allocDecls_lookup`). Temps are write-then-read within one
  statement, never captured or address-taken — sharing is unobservable.
- **D6 (ROUTINE) — per-iteration loop variables and `goto`.** Mechanism unchanged (the frontend's per-iteration copy, now a body-block decl;
  probe p1 + the `for-loopvar-*` rows). The `goto` hoist envelope stands; RECORD in FR-11 that block-entry allocation gives a hoisted variable
  ONE cell per function-body entry, so the refusal of captured/address-taken hoists (emit.go:2735–2760) is load-bearing — gc gives a fresh
  cell per pass (probe p2). An early `return`/`break` over a declaration leaves a private cell of §3, never referenced.
- **D7 (ROUTINE) — named results, defers, zero values.** Results are allocated at frame entry (`enterFrame.plan`, Machine.lean:898–906),
  untouched; `pushDefer` (:3974) saves argument VALUES while a closure's `captured : List GoValue` (Value.lean:908) holds cell addresses — the
  «captured variable vs saved defer argument» distinction is already in the data. Zero value at entry, initializer at the source point:
  `defaultValue` (Ops.lean:2470–2522) refuses only `Ty.unsupported`/opaque/interface-at-index — such a refusal would now fire at block entry,
  BEFORE output the block printed first: expected on 0 rows, detected by the trace's `obsHash`, any hit reported.
- **D8 — the layout as a FUNCTION (request 4) and the lifetime lemmas, by intended name.** `def entrySlot (s : Store) (i : Nat) : Loc :=
  .base ⟨s.heap.size + i⟩` — ONE function for both entries: frame entry binds `args[i] ↦ entrySlot s i`, `results[j] ↦ entrySlot s
  (args.size + j)` (the existing `enterFrame_lookup_arg/_result` restated through it); block entry binds `decls[i] ↦ entrySlot s i`. Lemmas:
  `blockEntry_shift` (`s'.heap.size = s.heap.size + decls.length`), `blockEntry_lookup` (the slot), `blockEntry_lookup_outer` (an undeclared
  id resolves as in `env` — shadowing by scope: `LocalEnv.lookup_pushScope` + `allocDecls_lookup_preserve`), `blockEntry_fresh` (new slots
  ≥ the old size: no existing value, env or label names them — `Store.alloc_shape`), `blockEntry_zero` (`defaultValue` normalized at the
  type — the C1 D3 premise), `blockExit_store_eq` (`seqDone` pops with the store unchanged — escaped/captured cells survive lexical exit),
  `heap_size_mono` (no step shrinks the heap — the `σ.nextAddr ≤ σ'.nextAddr` conjunct of `step_preserves_wf_loc`, StateWf.lean:8422, named),
  `frameEntry_fresh` (two activations never share a slot), `pushDefer_saves_values` / `funcVal_captures_locs` (the D7 pair as equations). All
  pinned in `BridgeSet.lean` (RE-PIN 7) and added to the core audit's required list.

## 5. Blast radius

Core: `Stmt` 44 → 43 constructors (the plan's «39» predates E13/`unseq`); `Step` 128 → 127 rules; `stepFn` loses `case13`
(MachineSound.lean:1756–1759) — the 112 positional tags there and 44 in `PrefixFacts.lean` after it shift by one (mechanical re-tagging, the C3
class); `StateWf` (`Stmt.locSup` :266, `step_preserves_wf` case :7598), `StepErrors` (`stepFn_strict`, one case fewer), `SyntaxEqb` :635/:731,
`Locals.declIds` :35, `Admission*` arms, `UnseqSound` + `StateWf`'s `unseqEnter` case (D3b). Theorem STATEMENTS unchanged: packet A/B
(`ExecutionStatement.lean`, `Prefix.lean`), BridgeSet rows 1–132 (D4 keeps 98–100); new rows for D8. Decoder: `NativeToIR.lean` only (W1) —
~20 emission sites become `declarePending`, the block closers change; `Tests/unseq-wire` wires untouched; hand-built tests rewritten
(UnseqScheduler.lean:310/:346/:742, GoCoreEval ×2, GoCoreContract ×2, the Admission fixtures). Wire/twin: UNCHANGED (W1) — the window plan's
«`--slow` (twin re-pin)» lapses; the train's 5a `--slow` still runs (compiled inputs change → provenance STALE, the r57 precedent): a provenance
refresh, observation set identical, `wire_sha256` unchanged (unlike r55/r57, where B6 moved it); dedup node/edge counts may move (§2 #8).
Expected row movements: NONE; watch list: the budget rows (§2 #10), any `defaultValue`-refusing row (D7). Choice trace: byte-identical per
consumption expected. Changelog: the C4 row of `docs/changelog/61958f2e-WINDOW.md` — the deletions, the fuel shift, no wire change.

## 6. Plan, estimate, stop rule, owners

S1 (Opus): the decoder threading + `.block decls` closers (W1, D5), the core deletion, D3b, hand-built tests; gate `scripts/capped scripts/ci
--diff`. S2 (Opus; Fable settles the D8 statements first): the re-tagging, the `UnseqSound`/`StateWf` cases, the D8 lemmas, BridgeSet RE-PIN
7, the audit list. S3 (Opus): the whole-corpus choice trace vs `main`, the detector-soundness matrix, the twin/certified checks (§5), records +
the changelog row, the audit ask and its fix round. **Estimate: 3–4 sessions + audit** (the plan's «2 + re-pin» / «2–3 + audit» under-counted
the positional re-tagging and the `unseq` rule; W1 removes the twin re-pin). **Stop rule:** G-C3's — a module slower than 1.5× (same box,
capped, locked; `Machine`, `StepFn`, `MachineSound`, `StateWf`, `MachineEqb`, `StepErrors`, `BridgeSet`) or any NEW/RAISED `maxHeartbeats` is
reported and the lane stops. Fable: this note (the audit), D3b's rule text, the D8 statements, the audit of the landed lane; Opus: everything
mechanical. Any §2 verdict overturned by a run is a STOP-and-report (invariant 2), never a re-pin.

## 7. Decisions for the [USER] — ALL NINE RULED as recommended, 2026-10-01 ([USER] Mike, relayed; the record at the top)

1. **Pass G-C4 in the scoped form of §3**, with §2's verdicts as the discharged precondition (no supported observation changes). Rec: YES. **RULED 2026-10-01: as recommended.**
2. **D2 = W1** — wire unchanged, decoder-side hoist; the lane's gate is `--diff` (plus the train's 5a `--slow`); no twin re-pin. Rec: YES. **RULED 2026-10-01: as recommended.**
3. **D3 = (b)** — `unseq` binder cells in a sweep-private scope at ENTER; the fixed-`.seq`-env law holds without exception. Rec: YES. **RULED 2026-10-01: as recommended.**
4. **D4** — keep `seqCont`'s equality splice; the 2026-09-04 «splice unconditionally» wording is withdrawn as unsound in general. Rec: YES. **RULED 2026-10-01: as recommended.**
5. **D1, D5–D7 as routine lane choices** (block-entry unit with the loop-body-is-a-block check; temp dedupe; the FR-11 note; results/defers untouched; zero at entry). Rec: YES. **RULED 2026-10-01: as recommended.**
6. **Channel 5 (`locJson` raw ids)** — RECORD as a standing limit of the observation schema, outside C4; canonicalizing it is a separate decision if a consumer ever pins reference-valued Lean observations. Rec: record, do not change here. **RULED 2026-10-01: as recommended.**
7. **Fuel** — accept the step-count decrease with no compensating no-op step; a budget-row flip is reported and ruled, never absorbed. Rec: YES. **RULED 2026-10-01: as recommended.**
8. **D8's layout function and lemma set** as the lane's acceptance list (BridgeSet RE-PIN 7, the audit list). Rec: YES. **RULED 2026-10-01: as recommended.**
9. **The estimate (3–4 sessions + audit) and the G-C3 stop rule** as the lane's bounds. Rec: accept. **RULED 2026-10-01: as recommended.**
