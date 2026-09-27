# The batched window — the execution plan (2026-09-24)

[AGENT] planning writer, lane `docs/window-plan-0924` (worktree `.claude/worktrees/window-plan-0924`, off `main` @ `3fb4a0d1`). The charter
rev. 2 (`docs/2026-09-23_batched-window-charter.md`) is the window of RECORD ([USER] Mike 2026-09-24, «I'm happy to go with your rec»,
relayed — `docs/2026-08-31_qrow-rulings.md`, «The window charter (rev. 2) and the Codex packaging — RULED (2026-09-24)»). This file is its
EXECUTION TABLE: every unit of work in order, with owner kind, the charter row it executes, what must have landed first, gate class, audit,
the [USER] touchpoints and the session estimate. **Standing rule: nothing here re-decides a ruling** — a unit that appears to need one
STOPS and poses it (`CLAUDE.md`: «Named design gates are HARD STOPS»). Every Lean name below was verified on `main` @ `3fb4a0d1`.

## 0. Legend

- **Owner kinds.** *Codex packet* = launched by the [USER] against a brief in `docs/codex-briefs/`; own branch + worktree; exact inputs,
  deliverables, acceptance, boundaries; ends branch-complete + a report, never merges (precedent: the two evaluation-order reviews,
  `docs/2026-09-15_evaluation-order-model-review.md`, `docs/2026-09-16_evaluation-order-model-v2-review.md`). *Fable lane* = conceptual/
  design work; *Opus lane* = mechanical build-out and review; both dispatched by the coordinator (charter §1). One writer per worktree.
- **Gate classes** (`CLAUDE.md`; always `scripts/capped`, under the box-wide lock — `docs/operational-lessons.md` «The box-wide build lock»):
  *fast* = `scripts/ci` (docs + Lean statements, no runtime change); *`--diff`* = `scripts/ci --diff` (every runtime change); *`--slow`* =
  `--diff` + full re-certification (wire/frontend/baseline pin moves, written reason). Any change under `GoLean/` turns the fast gate's
  `certificate provenance` step red (STALE records, `tools/certification.py`) until the train's step 5a — expected, named, never fixed by a lane.
- **Audit** = the pre-merge adversarial audit; the ask is unconditional, trim/waiver is the [USER]'s.
- **[USER] touchpoints** (ledger 2026-09-24, «Left open»): each train's merge sign-off + audit trim; the design gates **G-P / G-C3 / G-C4**
  (HARD STOPS, `docs/2026-09-03_design-hygiene-arc.md`); any (b) pin, new entry class or unsound lift an E6 slice turns up; the LAUNCH of each
  Codex packet; (7) dry-run access at the offer; (11) the CLAUDE.md wording at row 2's landing; any push or tag.

## 1. The units, in execution order

| # | Unit | Owner | Executes | Prerequisites (landed on `main`) | Gate | Audit | [USER] touchpoints | Sessions |
|---|---|---|---|---|---|---|---|---|
| 0a | FIXTURE INVENTORY (F3): the pinned production frontend — `GO111MODULE=off GOCACHE=$PWD/artifacts/go-build-cache go run ./tools/nativefrontend --dir <fixture> --out .tmp/inventory/<unit>.wire.json` — over the fourteen `examples/fixtures/*` of `/home/dev/projects/golean-logic` @ `b2c37c1` (READ-ONLY; their `manifest.tsv` names the units) and every generated positive variant; per unit: source pin, frontend pin (our commit + receipt hash), go toolchain pin, EXPORT STATUS; recursive JSON count of `"stmt":"unseq"` and every graph-body kind; a failed export is NEVER «zero graphs»; `scripts/lower-diagnose` explains failures only; note `docs/2026-09-24_fixture-inventory.md` (counts + provenance; wires stay scratch) | Opus, NOW | charter row 0 (inventory) | none | fast (docs only) | ask | merge sign-off | 1 |
| 0b | PACKET A — CONTRACT: `GoLean/GoCore/BridgeSet.lean` (24 statement pins), `GoLean/GoCore/ExecutionStatement.lean` + `docs/2026-09-24_execution-statement.md` (charter §2 as checked `Prop` definitions, statements only), `docs/changelog/61958f2e-WINDOW.md` (live changelog draft) | Codex, NOW | row 0 (records/contract); `docs/codex-briefs/2026-09-24_packet-A-contract.md` | none (`main` @ `3fb4a0d1`) | fast + `check-core-audit` | ask | LAUNCH; merge sign-off | 1–2 |
| 1a | E6a — non-main units + the panic-vs-panic trigger refinement + the twin re-pin (written reason) + decoder follow-ups F8/R1 + the status-diverse manifest row | Fable | row 1 / E6a | none (‖ 0a, 0b: disjoint files) | `--diff` + `--slow` | ask | merge sign-off; any (b) pin / new entry class / unsound lift → STOP | 2–3 |
| 1b | E6b — element/field address operands `&a[i]`, `&s.f` (today `unseqAddrOperandRefusal`); `&*p`, `&pkg.V` dispositioned | Fable | row 1 / E6b (approved as a slice, decision 5) | 1a | `--diff` | ask | merge sign-off; same STOP rule | 1–2 |
| 1c | E6c — `recover()` inside a lifted body: design first, then admit or refuse BY NAME with the reason | Fable | row 1 / E6c | 1b | `--diff` | ask | merge sign-off; same STOP rule | 1–2 |
| 1d | E6d — the nine singletons, per-function disposition (admit via a named axis, or a stated reason it cannot be a legacy emitter) | Fable | row 1 / E6d | 1c | `--diff` | ask | merge sign-off; an admit that opens a whole axis is POSED | 1–3 |
| 1e | E6e — RETIRE `Stmt.unseqProbe` / `Cont.probeK` / `Step.unseqProbe` / `ChoiceSite.unseqPanic` at census ZERO (corpus + twin) with preservation evidence; the MachineSound re-proof; changelog lines | Fable | row 1 / E6e | 1d AND zero on both sweeps; if any slice was REFUSED, 1e does not run — the triple stays, flagged; the window continues at 2a | `--diff` + `--slow` | ask | merge sign-off | 1 |
| 2a | LABEL RESHAPE — `StepLabel := { trace : AccessTrace, picks : List PickRecord, out : List GoString }` as `Step`'s fifth argument and `stepFn`'s fourth component; `StepEvent := { who, action, label }`; silent projection PRESERVED (`⟨[],[],[]⟩`, the fold); `stepFn_sound` / `step_complete` / `program_run_iff` / `observation_iff` re-proved; `BridgeSet.lean` re-pinned; changelog lines. Lands on the LANE TIP first; Codex forks from it | Fable/Opus | row 2, first half | 0b; 1e (or its flagged non-run) | `--diff` | one audit with 2b | merge sign-off of the COMBINED candidate; (11) the CLAUDE.md wording POSED at landing | 2–3 |
| 2b | PACKET B — BRIDGES: `Prefix` / `Finish` / `LRun` proved over the reshaped `Step`/`stepFn`; erasure, `stepFnIter` agreement, the fuel bridges with `ZeroCost`, replay COVERAGE, the refusal-separate correspondence + domain corollary, the single-goroutine embedding with a PROVED cost relation, the silent-projection lemma | Codex | row 2, second half; `…_packet-B-bridges.md` (coordinator refreshes input commit + label type) | 2a's tip | `--diff` + `check-core-audit` | (with 2a) | LAUNCH; merge sign-off (one train) | 2–3 |
| 3 | P — native method promotion, `Func.wrapper` deleted; the §4 P preservation list; NAMED replacements in the migration table (`recoverThroughWrappers`, `methodInfoByFuncId?`, `findFunctionIn?` changes) | Fable | row 3 | 2a + 2b | `--diff` + detector re-run | ask | **G-P HARD STOP** before dispatch; merge sign-off | 3–4 |
| 4 | PACKET C — `Cont := List Frame` (constructor names as `@[match_pattern] abbrev`s); ZERO behaviour change; `BridgeSet.lean` re-pinned; changelog | Codex | row 4; `…_packet-C-continuations.md` (refreshed after 3) | 3 | `--diff`, baseline UNCHANGED | ask | **G-C3 HARD STOP**; LAUNCH; merge sign-off | 3–4 |
| 5 | B6 — numeric locals + a CHECKED source/debug table; «IDs stable across source edits are NOT an API promise» | Opus | row 5 | 4 | `--diff` (+ `--slow` if the wire schema moves) | ask | merge sign-off | 2–3 |
| 6 | C4 — block-entry allocation: the address-sensitive-ESCAPE AUDIT first (Fable), then the reshape (Opus); the SCOPED preservation claim (decision 9); `Stmt.initialization` deleted | Fable (audit) + Opus | row 6 | 5 | escape audit → `--diff` + `--slow` (twin re-pin) | ask | **G-C4 HARD STOP** (re-posed when reached, with the audit's findings); merge sign-off | 2–3 + audit |
| 7a | PACKET D — per-arm `stepFn` EQUATIONS over the final shape; the named rewrite set; the toy semantic-equation CLIENT (`Tests/EquationClient.lean`); the `scripts/check-equations` gate; `BridgeSet.lean` additions; changelog candidate freeze | Codex | row 7 (equations; decision 8); `…_packet-D-equations.md` (refreshed after 6) | 6 | `--diff` + `check-core-audit` + `check-equations` | ask | LAUNCH; merge sign-off | 2–4 |
| 7b | The RE-PIN OFFER — tag `customer-pin/<date>`; the changelog FROZEN at the exact commit; three checks green (statements, equations, client); the offer STATES ITS LIMITS (charter §2 tail); OPTIONAL isolated-clone dry run under gitignored `deps/` | Opus (records) | row 7 | 7a | `--slow` + the round's certification receipt | ask | (7) dry-run access; the TAG and any PUSH are separate sign-offs | 1 |
| CL | CORPUS LANES CL1–CL5 (charter §4): direct methods + multi-field records; byte-slice reads + `encoding/binary` + nil-map; call/return/unwind (write-call-panic, observation-before-failure); slices/ring buffers; callbacks/Storage/timers. Every row a differential row; a miniature fixture is NEVER «a proof of Raft» | Opus, PARALLEL | §4 | none (files disjoint from the core lane: `Corpus/`, `baselines/`, ledgers) | `--diff` per landing | ask per landing | merge sign-off; a PASS→non-PASS flip needs a `BUGS.md` Cases line | 1 each |

## 2. Serialization and parallelism

- **ONE CORE WRITER.** `GoLean/GoCore/` has one lane at a time: 0b → 1e (its core deletion) → 2a → 2b → 3 → 4 → 5 → 6 → 7a. Packet B forks
  from 2a's LANE TIP and the two merge as ONE candidate (response §Recommendation: «dependent changes need a combined candidate»). Packets C
  and D fork from `main` after 3 and after 6. `BridgeSet.lean` belongs to whichever lane holds the core; a row that changes a pinned
  statement re-pins it in the SAME commit and writes its changelog lines (`docs/changelog/61958f2e-WINDOW.md` is LIVE; 7b freezes it).
- **ONE FRONTEND WRITER.** 1a → 1b → 1c → 1d → 1e serial (all touch `tools/nativefrontend/unseq.go` + the decoder `GoLean/NativeToIR.lean`).
- **PARALLEL, and nothing else:** 0a ‖ 0b ‖ 1a; CL ‖ everything; the coordinator's records work ‖ everything.
- **Codex packets run against the brief as REFRESHED by the coordinator** (input commit, label type, line numbers); a brief marked DRAFT
  is not launchable. A packet that must choose between materially different readings STOPS and writes both (each brief's ambiguity policy).
- **Per item, the merge protocol exactly** (`CLAUDE.md`): gate green (class above) → the audit ask → at-that-moment sign-off → `--ff-only`
  → step 5a (`refs/snapshots/<round>/main`; `scripts/build-certified`; `release-check`; a changed certified set is a finding, not a re-pin)
  → parked on `main`, clean, green. 1a/1e/6's `--slow` runs carry a written re-pin reason.
- **ONE re-pin offer at close (7b).** Nothing reaches the customer before it; no interim pin, no calendar deadline (response §7 Q10). The
  offer carries the changelog, `BridgeSet.lean`, the equation file and the client green, the `ci --diff` tail + certification receipt, and
  STATES ITS LIMITS: the program bridge ASSUMES successful setup, RETAINS `initPrintRefusal?` (decision 10), DEFERS pool/registry coverage;
  the restricted sequential result does NOT discharge the whole owed simulation (charter §2 tail; review).
- **Sessions** ([AGENT] estimate, charter §6): ≈ 24–37 serial, ≈ 20–30 with the parallel lanes.

## 3. Planning choices made here ([AGENT], inside the charter's letter; overturnable by the coordinator or the [USER] before launch)

1. `Prefix` is DEFINED by executable steps — `stepFn`-threaded, the labelled `Trace` (`GoLean/GoCore/Trace.lean:15`) — reading the
   charter's «n executable steps; the tape threaded by consumeAtE» literally; the relational view is erasure to `Steps` + `stepFn_sound` /
   `step_complete`; a `Step`-primary variant is a DERIVED theorem after the reshape, not a second carrier (`Step` stays primitive as ruled).
2. Packet A pins `stepFn`, `stepFnIter`, `iter_iff_trace` beside the proposal's 21 (their §6 bullet 1 names them; statements settled today).
3. For TODAY's shape (no `picks` in the label yet) the choice-replay coverage statement is written by RECORD through `seqConsumption`
   (`Machine.lean:5190`) + `Choices.consumeAtE`; packet B restates it over `StepLabel.picks`. Packet A flags `stepFn_consumption_some`'s
   `c.appendTargetLocal` premise as packet B's first question rather than baking it into the statement.

**Execution model changed ([USER] 2026-09-27).** Every «Codex packet» row runs as an Opus 5.5 SUBAGENT dispatched by the coordinator against the same brief; no [USER] launch step. Rows 1b–1e (E6b–E6e) are OFF the critical path (legacy triple survives into the re-pin).
