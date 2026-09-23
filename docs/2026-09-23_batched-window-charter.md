# The batched breaking window — charter (2026-09-23)

[AGENT] planning writer, lane `docs/roadmap-customer-alignment-0922`. The window the proposal posed
(`docs/2026-09-23_proposal-to-logic-team.md`) REVISED under the logic team's response
(`docs/2026-09-23_response-from-logic-team.md`, verbatim copy; «§n» below cites it). Rulings: `docs/2026-08-31_qrow-rulings.md`,
the four records from «Roadmap review requested (2026-09-22)» on. Names are `main` @ `9269912e` (verified). **[inf]** marks an
inference. Nothing here is decided: §7 lists the decisions, all PENDING [USER].

## 0. Status

| Standing | What | Provenance |
|---|---|---|
| RULED | ONE window, ONE re-pin offer after it, with a changelog: «I think we'll want to give them one repin after all the breaking changes have landed. Can we batch these together» | [USER] Mike 2026-09-22/23, verbatim, relayed |
| RULED | the sequential label is the FULL event label: «we should make the model as regular as possible» — inside the window, before C3 | [USER], same |
| RULED | NaN [a]+[b] DEFERRED: «if this isn't in the target, we can defer it» | [USER], same |
| RULED | item 4 — a named stable set + per-pin changelog, equation lemmas if asked, NO facade: «Right, I agree regarding item 4, let's see what that team asks for» | [USER] 2026-09-23, relayed |
| RULED | the branch stays unmerged during their review: «We can leave it on a branch while they look at it» | [USER] 2026-09-23, relayed |
| ENDORSED | the batch; order **E6 → label + execution bridges → P → C3 → B6 → C4**; E6 inside as the first item; `{trace, picks, out}`; `BridgeSet.lean` + equation lemmas over the FINAL shape; records NOW; NaN/profiles/no-`Language`-spike deferrals | logic team §Recommendation, §3, §6, §7 Q1–Q8 |
| REQUIRED | five corrections to the execution statement (`Prefix`/`Finish` primary, `LRun` derived); conditions on P/B6/C4/C1; the confluence claim withdrawn; NPDRF stays unusable; universal refusal exclusion retained on their side | §1, §2, §4, §7 tail |
| PROPOSED | everything below; the logic team's conditions are adopted as [AGENT] proposals, PENDING [USER] (§7) | [AGENT] |

## 1. The window

Lane models: Fable = conceptual/design work; Opus = mechanical build-out and review; Codex = deep clear-spec theorem work ABOUT the
semantics on a separated lane (memory `refinedgo-target-and-codex-lanes`). Gate classes: `--diff` = `scripts/capped scripts/ci --diff`
(every runtime change); `--slow` = the full run with certification (wire/frontend pin moves); every item gets the pre-merge audit.

| # | Item | Contents | Conditions adopted (cite) | Exposure owed | Gate | Sessions | Lane |
|---|---|---|---|---|---|---|---|
| 0 | NOW — records/contract | `GoLean/GoCore/BridgeSet.lean` (new; the proposal's 21 names as `example : <pinned statement> := <name>`, in the default build so drift FAILS the build; §6 families added as their statements settle); the changelog `docs/changelog/61958f2e-<close>.md` (new dir) kept LIVE through the window, exact target frozen at close; the execution-statement DESIGN NOTE (= §2 here, expanded: `Prefix`/`Finish`, the five corrections, the fuel/refusal/choice-replay conventions stated exactly); the fixture INVENTORY: re-lower their fourteen `examples/fixtures/*` + generated positive variants with `main`'s frontend (`scripts/lower-diagnose`; grep `"stmt":"unseq"`) and report `unseq` entry HONESTLY — the «none enters a graph» claim is a hypothesis until then (§1) | §1 (re-lower all fourteen + variants); §6 («start the statement and inventory work now»; pin statements AND equations); §7 Q4, Q7 | none new — an inventory of what exists | `scripts/ci` (BridgeSet compiles; no runtime change); inventory = scratch under `.tmp/`, results in the note | 1–2 | Fable (design note) + Opus (BridgeSet, changelog, inventory) |
| 1 | E6 | unchanged contents (`docs/2026-09-22_unseq-stage-e5-handoff.md` §2/§3): the trigger refinement («… or against another FAILING occurrence», RATIFIED 2026-09-22); the graph grammar widened to NON-MAIN units + the twin re-pin with a written reason; the legacy triple RETIRED at census zero (`Stmt.unseqProbe`, `Cont.probeK`, `Step.unseqProbe`, `ChoiceSite.unseqPanic`); the two decoder follow-ups (F8 named refusal for an `after` edge on a literal `allocate`; R1 decoder-wide cross-check of every source-local atom's annotation against its `declare`); the owed status-diverse manifest row (`expected_status` set) | §7 Q2 (inside, first, «no extra re-pin or artificial delay») | none new; changelog lines: one `Cont` ctor, one `Step` rule, one site fewer | `--diff` + `--slow` (twin re-pin) + audit | 2–3 | Fable |
| 2 | Label + execution bridges (ONE combined candidate: «dependent changes need a combined candidate», §Recommendation) | `StepLabel := { trace : AccessTrace, picks : List PickRecord, out : List GoString }` as `Step`'s fifth argument and `stepFn`'s fourth component; `StepEvent := { who, action, label : StepLabel }` — one label type at both layers. SILENT PROJECTION PRESERVED: the label is a FIELD of the step, not an element appended to an event stream; a pure step's label is `⟨[], [], []⟩`; the observation is the FOLD (`execProgLoopOut`'s `out` fold, the `AccessTrace` flatten) so a pure step contributes NOTHING and no `[emptyLabel]` ever appears where today there is none; a pinned lemma states `silent ⟨[],[],[]⟩` projects to `[]` for an adapter (§3). Then §2 below: the `Prefix`/`Finish` closure with its theorems | §2 (1)–(5); §3 (per-channel order; no total interleaving — DOCUMENTED, not invented; `initPrintRefusal?` scope stated); §7 Q3, Q6 | §6 bullets 1–3: prefix composition/erasure/executable correspondence; terminal classification, rendering/consumption, output projection; `consumeAtE` replay/projection + consultation coverage; the sequential/pool cost or stuttering correspondence | `--diff` (fuel-exact) + audit | 4–6 | Fable/Opus (the reshape) → Codex (the closure, bridges, coverage; forks from the reshape's tip) |
| 3 | P — native method promotion (`Func.wrapper` deleted) | as proposed; PRESERVE: receiver evaluation once, pointer/value receiver adjustment and copying, embedded-field traversal, nil behaviour, package-qualified method identity, method-value receiver capture at CREATION, direct-`recover` eligibility and deferred receiver/argument capture when wrappers vanish | §4 P | declaration lookup + the resolved receiver path/entry EQUATIONS (their `MaybeUpdate` pilot uses ordinary call rules); `recoverThroughWrappers`/`methodInfoByFuncId?`/`findFunctionIn?` changes → NAMED replacements in the migration table, no fake aliases (§6) | `--diff` + detector re-run + audit | 3–4 | Fable |
| 4 | C3 — `Cont := List Frame` | as proposed (constructor names survive as `@[match_pattern] abbrev`s); NOT a context-fill law | §Recommendation: «a useful simplification, not a prerequisite for our CPS bind» — no added condition | `pushDefer`, `seqCont`, frame exit, `Cont.rebuild_*` as list laws | `--diff` + audit | 3–4 | Fable/Opus |
| 5 | B6 — numeric locals | declaration IDs + a CHECKED source/debug table (`scripts/check-*`-class gate on the table); a lexical ID ≠ an activation's heap location — recursion, re-entered blocks, loop variables, escaping captures get fresh runtime identity where source semantics does; shadowing, same-block short-declaration reuse, argument/result slots, capture mappings preserved; clause: **numeric IDs stable across source edits are NOT an API promise** — the checked metadata lets their source admission reconstruct bindings after renumbering | §4 B6 | the table + lookup lemmas | `--diff` (+ `--slow` if the wire schema moves) + audit | 2–3 | Opus |
| 6 | C4 — block-entry allocation | storage ALLOCATION separate from INITIALIZER execution (initializer calls, reads, failures, binding visibility at the source point); lifetime: captured/escaped cells survive lexical exit, distinct dynamic activations, defer references, named result storage, per-iteration variables; «up to heap isomorphism» SCOPED: an injection with extra private cells + stuttering over a STATED observable domain, not a bijection; an ADDRESS-SENSITIVE-ESCAPE AUDIT (`%p`/pointer formatting, pointer↔`uintptr` conversion, `repr`, dedup certificates) BEFORE any preservation claim; pointer equality and aliasing preserved | §4 C4 (supersedes the proposal's unscoped «up to heap isomorphism»; refines the G-C4 caveat — flagged §7) | block layout/allocation, lookup preservation, zero-value/type normalization, freshness/frame lemmas (replacing `initialCells`, `declareRoots`, result-address arithmetic compositionally) | escape audit → `--diff` + `--slow` (twin re-pin) + audit | 2–3 + audit | Fable (audit) + Opus |
| 7 | The re-pin OFFER | tag `customer-pin/<date>` on `main`; the changelog FROZEN at the exact commit — changed constructors, wire schemas, choices, allocations, fuel, refusals, theorem premises; `BridgeSet.lean` green + a SEMANTIC-EQUATION gate + one small INDEPENDENT in-repo consumer green (§6; the consumer's shape is decision 7); equation lemmas over the FINAL shape (priority §3); the `ci --diff` tail + the round's certification receipt; OPTIONAL isolated-clone dry run (`deps/`, gitignored, capped, independent caches; PENDING [USER] access — evidence, NOT their acceptance, which is `scripts/check` + their theorems + their three consumers) | §6, §7 Q4, Q5, Q10 | the equation families | `--slow` + audit | 3–5 | Codex (equations) + Opus (records) |

## 2. The execution statement, corrected

Specification sketch (§2 of the response), not Lean; the design note of row 0 is its expansion. `Step` stays primitive.

```text
Prefix pctx n (c, s, ch) ls (c', s', ch')        -- n executable steps; ls : List StepLabel, one per step; the tape threaded by consumeAtE
Finish pctx (c', s', ch') fl outcome              -- the driver's classification + final effects/choices fl
  normal  : c' = .next .stop                                   → .normal s' ch'                  fl = silent
  blocked : c' blocked (single goroutine, no partner: sequential deadlock, its environmental condition stated)  → .deadlock s' ch'
  aborted : Config.abort? c' = some (first, rest) ∧ consumeAtE .repanicCollapse (repanicCollapseWidth first rest) ch' = (pick, ch'', rec)
            ∧ abortMsg pctx first rest pick = .ok t             → .aborted t s' ch''              fl.picks = rec  (the terminal draw)
LRun pctx (c,s,ch) ls fl o  :=  ∃ n c' s' ch', Prefix … n … ls (c',s',ch') ∧ Finish … fl o      -- DERIVED, not the carrier
```

The five corrections → theorems we OWE ([AGENT], adopting §2): **(1)** every outcome carries the endpoint store and residual tape
(the proposal's `.aborted (Terminal)` lost them); `execStmtLoop`'s result is a PROJECTION of `LRun`'s outcome — the CLI's shape is
unchanged. **(2)** `Finish.aborted` is a PROVED terminal transition doing exactly what `stepFn`'s `.panicking chain .stop` arm does
(`abortConsult` = `consumeAt .repanicCollapse`, then the fallible `abortMsg`); `abortLeftover` is its residual tape; an `abortMsg`
error is a REFUSAL, reported by (5) — never a silent stuck. **(3)** fuel, exactly as today: `execStmtLoop` classifies `.next .stop`
and the blocked forms BEFORE the `fuel` match; an abort is thrown inside `stepFn`, so it needs `fuel + 1` — PRESERVED. Bridges:
`= .ok (sf, chf) ↔ ∃ n ≤ fuel, ls, Prefix n … ls (.next .stop, sf, chf)` (today's `run_ok_iff`, labelled); `= .error .fuelOut ↔ ∃ ls c' s' ch',
Prefix fuel … ls (c', s', ch') ∧ ¬ classified c'` (the fixed tape's ACTUAL prefix of length `fuel`, nothing classified in budget —
no «every run is longer»); `Prefix`'s refl/composition/splitting/erasure-to-`Steps`/exact-`stepFnIter`-agreement hold for every `n`,
independent of termination, so earlier labels survive fuel-out and divergence. **(4)** replay by RECORD: every consultation is a
`consumeAtE site bound ch` with its `PickRecord` (bound ≤ 1 → no record; empty tape → pick 0; modulo selection as `Choices.consume`);
COVERAGE: `stepFn ctx s c ch = .ok (c', s', ch', l) → ∀ ch₂, replays l.picks ch₂ ch₂' → stepFn ctx s c ch₂ = .ok (c', s', ch₂', l)` — no
unrecorded consultation affects a step; fixed-tape soundness/completeness (`stepFn_sound`/`step_complete` relabelled) + the witness
direction for arbitrary legal steps. **(5)** refusal SEPARATE: the unconditional `execStmtLoop fuel s c ch = r ↔ r ∈ {ok, terminal, fuelOut,
refusal}` classified by `Prefix`/`Finish`/a refusing `stepFn` call — no «all executions succeed» premise; THEN the corollary under a
proved reachable-state domain invariant (`step_preserves_wf` + what we can prove of no-refusal for the reached fragment); discharging
the domain facts for a source fragment stays theirs (§2 (5): «Our fragment rules will discharge the appropriate domain facts»).

Program level (one composable account): `runProgramSetupM … = .ok (pctx, c₀, s₀, locs, ch₁)` is the premise (setup's tape `ch → ch₁`
INCLUDED); readout `loadMany pctx sf locs`; output = the `out` fold. **`initPrintRefusal?` scope** ([AGENT], PENDING): the bridge covers
setup's choice consumption and states that init OUTPUT is empty BY REFUSAL (`runInitConfig` throws on `printOut?`) — the named
limitation is RETAINED in this window, not lifted (§3: «otherwise retain the named limitation»). Single-goroutine EMBEDDING first:
`execProgLoop_single`/`seqOpCount` restated over `StepLabel` with a PROVED cost or stuttering relation — never «equal fuel» asserted.
**The pool half WAITS for**: the labelled pool relation over `StepLabel` with attribution and terminal events (`program_run_iff`,
`observation_iff` relabelled), registry boundaries, pool deadlock's own condition — after the window (§2: «need not block this window»).

## 3. Owed exposures by module

| Module | Laws / equations owed | Cite | Priority |
|---|---|---|---|
| Control, calls, defer (`Machine.lean`, `StepFn.lean`) | final method resolution + receiver entry (`enterFrame`/`enterFramePick`), parameter/result/capture layout, `pushDefer` registration and draining, `stepFrameExit`, return, panic/`recover` boundary (`recoverResult`), `seqCont`; per-arm `stepFn` equations over a SYMBOLIC continuation/environment/state with explicit operation premises; a NAMED rewrite set / `simp only` examples, no global unfolding | §4 P, §6 bullets 1, 5; §7 Q5 | 1 |
| Memory (`Ops.lean`: `loadLoc`, `storeLoc`, `Store.alloc`, `normalizeValueForTy`) | the allocation-NORMALIZATION premise stated; read/write/frame/freshness laws; initialization/preservation lemmas + LOCAL operation premises from which the logic maintains its invariant — no unexplained global well-formedness assumption per client; later: header/backing/sublocation/disjoint-update relations for slice borrowing | §4 C1, §6 bullet 4 | 2 |
| Blocks (C4) | block layout/allocation, lookup preservation, zero-value/type normalization, freshness/frame lemmas | §4 C4 | 2 |
| Choices (`State.lean`: `consumeAtE`) | replay/projection laws (`consumeAtE_fst_snd`, `_le_one`, `_of_lt` exist); exact per-step and terminal consultation coverage; the `repanicCollapse` terminal draw | §6 bullet 3 | 1 (with row 2) |
| Prefix/terminal/output (`Trace.lean`, `ProgramTrace.lean`, `MultiSound.lean`) | `iter_iff_trace`, `Trace.erase`, `run_ok_iff` relabelled; composition/erasure/executable correspondence; terminal classification, rendering/consumption, output projection; `runProgramM`/`runProgramPoolOutM` setup/readout composition + the cost/stuttering correspondence | §6 bullets 1–2 | 1 |
| Then | sequence/block/local initialization, branches, scalar loads/stores, record/map operations, allocation | §6 | 3 |

## 4. Corpus staging (fidelity lanes; the customer's fixture shape is the FIRST row of each; §5, §7 Q9)

1. Direct methods + multi-field records — pointer receiver, field paths/copies, declared integer widths + `uint64` wrap, unrelated
   state framed, two successive calls (their `Progress.MaybeUpdate` shape). 2. Byte-slice reads + `encoding/binary` + nil-map — nil/empty
   no-op, ≥ 8 bytes little-endian, missing key → zero, lengths 1–7 an EXPLICIT panic case (their `readOnly.recvAck`). 3. Call/return/
   unwind — write-call-panic (the write survives), observation-before-failure, deferred cleanup under Go control; Go `error` vs panic
   vs refusal kept DISTINCT (their `SentEntries`). 4. Slices/ring buffers — header copies share backing, `append` reuse/replace,
   reslice aliases, overlapping `copy`, nil vs empty, bounds failures + access labels. 5. Callbacks/Storage/timers — function-value
   and interface dispatch identity, effect boundaries, external-call CONTRACTS or NAMED refusals (`globalRand.Intn` is an environment
   contract, not a scheduler pick); no assumed postconditions. LATER: loops/`range`/map iteration; goroutines/`select` (not needed for
   `recvAck`). Every row is a differential row (`--diff`); a miniature fixture is NEVER reported as a proof of Raft (§5). Aliasing stays
   REAL in GoLean (§5 cross-cutting); choices are coupled by MEANING on their side — we preserve call + choice evidence, no tape equality.

## 5. Corrected and deferred items

- **`unseq` confluence — WITHDRAWN as stated** (§7 tail): `Tests/unseq-wire/src/w1/main.go` — `a := 1; mut := func() int { a = 2; return 0 };
  v := mut() + a`, one goroutine, permitted `{1, 2}`. DEFERRED, restated: a COMMUTATION theorem for unordered occurrences under an
  INDEPENDENCE hypothesis (disjoint read/write sets, no failing occurrence) — owed, unscheduled; the actual choices are preserved meanwhile.
- **NPDRF** — `GoLean/GoCore/NPDRF.lean`'s reduction stays EXPLICITLY UNUSABLE as stated (§7 tail); the access-granularity debt is
  retained in `CLAUDE.md`'s words; no concurrent concrete-Go coverage claim without a sound observational reduction or the finer semantics.
- **NaN** — DEFERRED ([USER]); BUG-094's plan stands without a lane. **Typed profiles** — PARKED ([USER] 2026-09-16). **No `Language`
  spike** — DROPPED (proposal §2; endorsed §7 Q8). **The pool/registry half** — after the window (§2). **Corrected reading** (§1): the
  logic's live backend is the refusal-observing `Safe` adapter, not `adequate_program_result` — the proposal's O-CLOSE premise reading is
  superseded; our (5) serves their universal refusal exclusion by making refusal a reported case, not a hidden premise.

## 6. Sequencing and lanes

- PARALLEL: row 0 ‖ row 1 (records touch `docs/`, `GoLean/GoCore/BridgeSet.lean`; E6 touches the frontend, decoder, `Corpus/`, baselines).
  Corpus lanes (§4) ‖ the core lane whenever files do not overlap (`Corpus/`, `baselines/`, ledgers vs `GoLean/GoCore/`).
- ONE CORE WRITER: `GoLean/GoCore/` has one lane at a time — rows 2 → 3 → 4 → 5 → 6 SERIAL (B6 → C4 serial per §Recommendation; the
  proposal's B6 ‖ C4 slot is withdrawn). `BridgeSet.lean` is row 0's until row 2 opens, then the core lane's; it is re-pinned per row.
- Row 2 is ONE candidate: the reshape lane lands first internally, Codex forks from its tip; they merge together (their §Recommendation).
- PER ITEM: the merge protocol exactly (`CLAUDE.md`) — gate green (class per row), the audit ask, at-that-moment sign-off, `--ff-only`,
  step 5a re-certification; a PASS→non-PASS flip needs a `BUGS.md` Cases line; every design gate (G-P, G-C3, G-C4) is a HARD STOP.
- ONE re-pin at close (row 7); NOTHING reaches the customer before it; no interim pin, no calendar deadline (§7 Q10).
- SESSIONS [AGENT estimate; precedents B7 one, C1 three + audits, `unseq` stages one each]: ≈ 20–30 serial, ≈ 16–24 with the parallel
  lanes (the proposal's 13–17 grew by the five corrections, the coverage theorem, the equations and the C4 audit).

## 7. Decisions for the [USER] (each PENDING; provenance [AGENT] proposal unless marked)

1. APPROVE this charter as the window of record (the order, contents, conditions and exposures of §1–§3).
2. AUTHORIZE the records/contract lane NOW (row 0; their §7 Q7 «Now for the contract and inventory»).
3. LAND this documentation branch (`docs/roadmap-customer-alignment-0922`): audit trim or WAIVER for a docs-only branch (posed 2026-09-23).
4. DISPATCH E6 as the window's first item (row 1; ruled 2026-09-22 as a lane, placed here by the addendum + their Q2).
5. Codex for the statement/bridges lane (row 2's closure, coverage and bridges; row 7's equations) as a separated lane forking from the reshape.
6. Dry-run ACCESS: a gitignored isolated clone of their tip under `deps/` at the offer (row 7) — evidence only; else the offer goes without it.
7. The «independent in-repo consumer» (their §6): read as a TOY `example` file rewriting by the equation set over a symbolic continuation —
   NOT an Iris `Language` instance (those were PARKED 2026-09-16 and CLAUDE.md's «we DO NOT ship any higher level reasoning» stands). Confirm.
8. C4's preservation claim: adopt their SCOPED form (injection + stuttering over a stated observable domain, escape audit first) as a
   REFINEMENT of the G-C4 caveat «up to heap isomorphism» ratified 2026-09-04 — the gate is re-posed when reached.
9. `initPrintRefusal?` — RETAIN the named limitation through the window (§2 above); lifting it is a later item.
10. CLAUDE.md's owed-simulation sentence («terminal priority») will need the `Prefix`/`Finish` wording at landing — a CLAUDE.md edit, [USER]-approved.
