# The batched breaking window — charter (2026-09-23, rev. 2)

[AGENT] planning writer, lane `docs/roadmap-customer-alignment-0922`. The window the proposal posed
(`docs/2026-09-23_proposal-to-logic-team.md`) REVISED under the logic team's response
(`docs/2026-09-23_response-from-logic-team.md`, verbatim copy; «§n» below cites it) and, in rev. 2, under the Codex review
(branch `review/batched-window-charter-0923` @ `28b12c50`, `docs/2026-09-23_batched-window-charter-review.md` + evidence
`docs/evidence/2026-09-23_batched-window-review/{FuelBoundary.lean,validation.json}`; «F1/F2/F3» cite it; dispositions in the
rulings ledger, «The Codex review of the window charter (2026-09-23)»). Rulings: `docs/2026-08-31_qrow-rulings.md`, the five
records from «Roadmap review requested (2026-09-22)» on. Names are `main` @ `9269912e` (verified). **[inf]** marks an inference.
Nothing here is decided: §7 lists the decisions, all PENDING [USER].

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
| REVIEWED | Codex review received ([USER]: «Window charter review landed from codex»): «support the direction; revise three points before treating this as an execution-ready charter» — F1 E6's exit accounting (P1), F2 the zero-cost classification predicate (P2), F3 the inventory procedure (P2); this rev. 2 applies all three; the review grants no authorization | review @ `28b12c50`; ledger record 2026-09-23 |
| PROPOSED | everything below; the logic team's conditions and the review's revisions are adopted as [AGENT] proposals, PENDING [USER] (§7) | [AGENT] |

## 1. The window

Lane models: Fable = conceptual/design work; Opus = mechanical build-out and review; Codex = deep clear-spec theorem work ABOUT the
semantics on a separated lane (memory `refinedgo-target-and-codex-lanes`). Gate classes: `--diff` = `scripts/capped scripts/ci --diff`
(every runtime change); `--slow` = the full run with certification (wire/frontend pin moves); every item gets the pre-merge audit.

| # | Item | Contents | Conditions adopted (cite) | Exposure owed | Gate | Sessions | Lane |
|---|---|---|---|---|---|---|---|
| 0 | NOW — records/contract | `GoLean/GoCore/BridgeSet.lean` (new; the proposal's 21 names as `example : <pinned statement> := <name>`, in the default build so drift FAILS the build; §6 families added as their statements settle) — STATEMENT checks only; the SEMANTIC-EQUATION checks and the toy client are separate files (row 7); the changelog `docs/changelog/61958f2e-<close>.md` (new dir) kept LIVE through the window, exact target frozen at close; the execution-statement DESIGN NOTE (= §2 here, expanded); the fixture INVENTORY (F3 procedure): run the PINNED PRODUCTION frontend — `tools/nativefrontend` as the certified receipt inventories it (`tools/certification.py` hashes `tools/`) — `GO111MODULE=off go run ./tools/nativefrontend --dir <fixture> --out .tmp/inventory/<fixture>.wire.json` for each of their fourteen `examples/fixtures/*` AND each generated positive variant, with an OWNED scratch `--out` per unit; record the source pin (their commit), the frontend pin (our commit + receipt hash), the go toolchain pin and the EXPORT STATUS per unit; count actual JSON statement nodes RECURSIVELY in the retained wire (`"stmt":"unseq"` and every graph-body kind); a FAILED export is reported as such, never as «zero graphs»; `scripts/lower-diagnose` explains failures ONLY (it deletes its probe wire; `--unseq-census` is a main-unit census, not the wire); counts + provenance go into the report, wires stay scratch. The «none enters a graph» claim is a hypothesis until then (§1) | §1; §6 («start the statement and inventory work now»; pin statements AND equations); §7 Q4, Q7; F3 | none new — an inventory of what exists | `scripts/ci` (BridgeSet compiles; no runtime change); inventory = scratch under `.tmp/`, results in the note | 1–2 | Fable (design note) + Opus (BridgeSet, changelog, inventory) |
| 1 | E6 — FIVE named slices (F1; table below) | E6a–E6d admit every residual legacy-probe emitter class; E6e retires the legacy triple at census ZERO. FIRST in the window because the retirement is the BREAKING part (one `Cont` ctor, one `Step` rule, one site fewer for a downstream `cases`); outside the window it would force a SECOND re-pin, against ruling 1 — the window absorbs the residual families rather than the customer absorbing a second port | §7 Q2 (inside, first); F1 (split; exit = whole-corpus + twin zero WITH preservation evidence; no grammar widening authorized by the review — each slice POSED, §7) | none new; changelog lines for the retirement | per slice below | **6–10** (was 2–3) | Fable |
| 2 | Label + execution bridges (ONE combined candidate: «dependent changes need a combined candidate», §Recommendation) | `StepLabel := { trace : AccessTrace, picks : List PickRecord, out : List GoString }` as `Step`'s fifth argument and `stepFn`'s fourth component; `StepEvent := { who, action, label : StepLabel }` — one label type at both layers. SILENT PROJECTION PRESERVED: the label is a FIELD of the step, not an element appended to an event stream; a pure step's label is `⟨[], [], []⟩`; the observation is the FOLD (`execProgLoopOut`'s `out` fold, the `AccessTrace` flatten) so a pure step contributes NOTHING and no `[emptyLabel]` ever appears where today there is none; a pinned lemma states `silent ⟨[],[],[]⟩` projects to `[]` for an adapter (§3). The existing UNCONDITIONAL program error accounting and coherence (`stepFn_sound`/`step_complete`, `program_run_iff`, `observation_iff`) are preserved through the reshape (review). Then §2 below: the `Prefix`/`Finish` closure with its theorems and the F2 cost accounting | §2 (1)–(5); §3 (per-channel order; no total interleaving — DOCUMENTED, not invented; `initPrintRefusal?` scope stated); §7 Q3, Q6; F2 | §6 bullets 1–3: prefix composition/erasure/executable correspondence; terminal classification, rendering/consumption, output projection; `consumeAtE` replay/projection + consultation coverage; the sequential/pool cost or stuttering correspondence | `--diff` (fuel-exact) + audit | 4–6 | Fable/Opus (the reshape) → Codex (the closure, bridges, coverage; forks from the reshape's tip) |
| 3 | P — native method promotion (`Func.wrapper` deleted) | as proposed; PRESERVE: receiver evaluation once, pointer/value receiver adjustment and copying, embedded-field traversal, nil behaviour, package-qualified method identity, method-value receiver capture at CREATION, direct-`recover` eligibility and deferred receiver/argument capture when wrappers vanish | §4 P | declaration lookup + the resolved receiver path/entry EQUATIONS (their `MaybeUpdate` pilot uses ordinary call rules); `recoverThroughWrappers`/`methodInfoByFuncId?`/`findFunctionIn?` changes → NAMED replacements in the migration table, no fake aliases (§6) | `--diff` + detector re-run + audit | 3–4 | Fable |
| 4 | C3 — `Cont := List Frame` | as proposed (constructor names survive as `@[match_pattern] abbrev`s); NOT a context-fill law | §Recommendation: «a useful simplification, not a prerequisite for our CPS bind» — no added condition | `pushDefer`, `seqCont`, frame exit, `Cont.rebuild_*` as list laws | `--diff` + audit | 3–4 | Fable/Opus |
| 5 | B6 — numeric locals | declaration IDs + a CHECKED source/debug table (`scripts/check-*`-class gate on the table); a lexical ID ≠ an activation's heap location — recursion, re-entered blocks, loop variables, escaping captures get fresh runtime identity where source semantics does; shadowing, same-block short-declaration reuse, argument/result slots, capture mappings preserved; clause: **numeric IDs stable across source edits are NOT an API promise** — the checked metadata lets their source admission reconstruct bindings after renumbering | §4 B6 | the table + lookup lemmas | `--diff` (+ `--slow` if the wire schema moves) + audit | 2–3 | Opus |
| 6 | C4 — block-entry allocation | storage ALLOCATION separate from INITIALIZER execution (initializer calls, reads, failures, binding visibility at the source point); lifetime: captured/escaped cells survive lexical exit, distinct dynamic activations, defer references, named result storage, per-iteration variables; «up to heap isomorphism» SCOPED: an injection with extra private cells + stuttering over a STATED observable domain, not a bijection; an ADDRESS-SENSITIVE-ESCAPE AUDIT (`%p`/pointer formatting, pointer↔`uintptr` conversion, `repr`, dedup certificates) BEFORE any preservation claim; pointer equality and aliasing preserved. The scoped theorem does NOT authorize changing an address-sensitive observation GoLean already supports: an observed mismatch is resolved or separately RULED, never declared outside the theorem after the fact (review) | §4 C4 (supersedes the proposal's unscoped «up to heap isomorphism»; refines the G-C4 caveat's STATEMENT while the behavioural gate stands — §7) | block layout/allocation, lookup preservation, zero-value/type normalization, freshness/frame lemmas (replacing `initialCells`, `declareRoots`, result-address arithmetic compositionally) | escape audit → `--diff` + `--slow` (twin re-pin) + audit | 2–3 + audit | Fable (audit) + Opus |
| 7 | The re-pin OFFER | tag `customer-pin/<date>` on `main`; the changelog FROZEN at the exact commit — changed constructors, wire schemas, choices, allocations, fuel, refusals, theorem premises; THREE separate checks green: `BridgeSet.lean` (statements), a SEMANTIC-EQUATION file (the equation lemmas PROVED, catching a definition changed under the same type), and one small INDEPENDENT toy client that USES the supported equations over symbolic state/continuations (never re-unfolds `stepFn`; GoCore only; in the test/contract graph with EXHAUSTIVE enrollment of the equation set; NO runtime dependency on it — decision 8); equation lemmas over the FINAL shape (priority §3); the `ci --diff` tail + the round's certification receipt; the offer STATES ITS LIMITS (§2 tail); OPTIONAL isolated-clone dry run (`deps/`, gitignored, capped, independent caches; PENDING [USER] access — evidence, NOT their acceptance, which is `scripts/check` + their theorems + their three consumers) | §6, §7 Q4, Q5, Q10; review | the equation families | `--slow` + audit | 3–5 | Codex (equations) + Opus (records) |

**E6's slices (F1).** Residue from `docs/2026-09-22_unseq-stage-e5-handoff.md` §3 and the census
`docs/evidence/2026-09-22_unseq-stage-e5/probes-e5d.txt` (58 corpus probes in 17 packages + 128 twin). Every slice is a grammar
widening POSED to the [USER] (decision 5); the review authorizes none. Zero reached by DROPPING or REFUSING a covered program, or by
silently fixing ONE order where the spec permits two, is NOT success: E6e's evidence is a fresh emission census (corpus + twin) AND
behavioural preservation — diff-one on every formerly-legacy row, the whole-corpus choice trace, gc draws inside every set that widens.

| Slice | Emitter class (census heads) | Contents | Gate | Sessions |
|---|---|---|---|---|
| E6a | NON-MAIN units (twin 128 `field-get`; corpus 23: `stdlib-source/{errors-join 5, strconv-parseuint 4, errors-wrap 3, frontier 3}`, `multipkg/mini-raft-twin` 7, `imported-goose/generics/generic-conversion` 1) + PANIC-vs-PANIC pairs with no effectful event (21: `builtins/len-vs-call-order` 15, `e13-sibling-panic-order` 6) | the grammar widened to non-main units + the twin re-pin (written reason); the trigger refinement «… OR against another FAILING occurrence» (RATIFIED 2026-09-22); the two decoder follow-ups (F8 named refusal for an `after` edge on a literal `allocate`; R1 decoder-wide cross-check of every source-local atom's annotation against its `declare`); the owed status-diverse manifest row (`expected_status` set) | `--diff` + `--slow` + audit | 2–3 |
| E6b | ELEMENT / FIELD ADDRESS operands `&a[i]`, `&s.f` (3: `e13-sibling-panic-order/{addrIndexLeftLenHoist, addrAssertLeftCall, arrayBaseTargetVsLen}`, heads `index-addr`) — today refused BY NAME in `tools/nativefrontend/unseq.go` `unseqAddrOperandRefusal` («outside the E5d grammar (E5z)») | the address of an element / field as an occurrence (a failing op: the index may panic; E5d admitted `&x` only); `&*p` and `&pkg.V` dispositioned in the same note; decoder arm; rows born per shape | `--diff` + audit | 1–2 |
| E6c | `recover()` INSIDE a lifted body (2: `recoverAssertVsLen$lit0`, `recoverAssertVsCallW$lit2`, heads `type-assert`) | lifting a body containing `recover()` must preserve its frame eligibility (direct-call-from-deferred rule) — a SEMANTICS-sensitive lift; design first, then admit or refuse BY NAME with the reason stated; rows born | `--diff` + audit | 1–2 |
| E6d | the NINE singletons — per-function disposition: `channels/recv-edge` `recvNilIndexBaseSecond$lit0` (`deref`); `channels/recv-map-elem` `mapKeyPanicDrains$lit0` (`index-get`); `fmt/sprintf-dyn` method `Infof` (`field-get`); `noodler/frontier2/array-of-funcs-indexed-call` (`index-get`, array base); `noodler/frontier2/typed-nil-error-return` (`binary`, interface comparison); `noodler/misc` `copyIntoArrayView` (`slice`, array); `noodler/strings`, `panic-recover/shim-refusal-unrecoverable`, `strconv/format-parse` — each an `Error` method (`field-get`, library-typed receiver) | each gets ONE of: ADMIT via a named E5z axis [inf: arrays as index/slice bases; interface conversion/comparison; method receivers of defined non-struct/library types; the indirection operand], or a STATED reason it cannot be a legacy emitter after E6a–c (e.g. the emitting function is refused earlier by name). An admit that opens a whole axis is its own family; the disposition may be «refuse by name, rowed» only where the program is NOT covered today | `--diff` + audit | 1–3 |
| E6e | the RETIREMENT at census ZERO (whole-corpus + twin — the RULED exit, not re-scoped) | `Stmt.unseqProbe`, `Cont.probeK`, `Step.unseqProbe`, `ChoiceSite.unseqPanic` deleted; the MachineSound re-proof for the removed rule; the fresh census + the preservation evidence above recorded; the changelog lines | `--diff` + `--slow` + audit | 1 |

Correction (2026-09-24, [AGENT] — the E6a audit fix round, the audit's F4b; records only, the row's text kept as ruled): the E6a row's «PANIC-vs-PANIC pairs with no effectful event (21)» mis-labels 7 of the 21 — `lenStructAnyKeyLeftAssert`, `convLeftCall`, `ifaceCmpLeftCall`, `sendChanIndex`, `assertReturnList$lit0`, `makeHintCall` and `lexerIdiom` contain an effectful call and were type-grammar refusals from the start; the class is 14 call-free + 7 with calls, all 21 named with each one's reason in the E6a design's closed / residue lists (`docs/2026-09-24_unseq-stage-e6-design.md` §E6a «the census»). The ruling record's «~30 rows» was loose; the census names 21 emitters.

## 2. The execution statement, corrected

Specification sketch (§2 of the response; F2 for the cost accounting), not Lean; the design note of row 0 is its expansion.
`Step` stays primitive. The driver's ZERO-COST classification is the five arms `execStmtLoop` (`StepFn.lean` ~1012) matches
BEFORE its `fuel` match — named exactly:

```text
ZeroCost c  :=  c = .next .stop  ∨  c = .blockedSend _ _ _  ∨  c = .blockedRecv _ _ _ _ _  ∨  c = .blockedSelect _ _ _  ∨  c = .blockedSync _ _ _ _
Prefix pctx n (c, s, ch) ls (c', s', ch')        -- n executable steps; ls : List StepLabel, one per step; the tape threaded by consumeAtE
Finish pctx (c', s', ch') fl outcome cost          -- the driver's classification + final effects/choices fl + FINISHING COST
  normal  : c' = .next .stop                                       → .normal s' ch'            fl = silent   cost 0
  blocked : c' one of the four blocked forms (single goroutine, no partner: sequential deadlock, its environmental condition stated)
                                                                   → .deadlock s' ch'          fl = silent   cost 0
  aborted : Config.abort? c' = some (first, rest) ∧ consumeAtE .repanicCollapse (repanicCollapseWidth first rest) ch' = (pick, ch'', rec)
            ∧ abortMsg pctx first rest pick = .ok t                → .aborted t s' ch''         fl.picks = rec   cost 1  (the stepFn call)
  abortRefused : … ∧ abortMsg pctx first rest pick = .error r      → .refused r s' ch''         fl.picks = rec   cost 1  (renderer refusal, reported)
LRun pctx (c,s,ch) ls fl o  :=  ∃ n c' s' ch' cost, Prefix … n … ls (c',s',ch') ∧ Finish … fl o cost     -- DERIVED, not the carrier
```

The five corrections → theorems we OWE ([AGENT], adopting §2): **(1)** every outcome carries the endpoint store and residual tape
(the proposal's `.aborted (Terminal)` lost them); `execStmtLoop`'s result is a PROJECTION of `LRun`'s outcome — the CLI's shape is
unchanged. **(2)** `Finish.aborted` is a PROVED terminal transition doing exactly what `stepFn`'s `.panicking chain .stop` arm does
(`abortConsult` = `consumeAt .repanicCollapse`, then the fallible `abortMsg`); `abortLeftover` is its residual tape; an `abortMsg`
error is `Finish.abortRefused`, a REFUSAL reported by (5) — never a silent stuck. **(3)** fuel, exactly as today and KEPT (F2): a
`ZeroCost` configuration is classified before the `fuel` match (cost 0); the abort is thrown INSIDE `stepFn`, so it needs `fuel + 1`
(cost 1). Bridges — completed runs bound PREFIX LENGTH + FINISHING COST: `execStmtLoop fuel s c ch = .ok (sf, chf) ↔ ∃ n ≤ fuel, ls,
Prefix n … ls (.next .stop, sf, chf)` (today's `run_ok_iff`, labelled; cost 0); `= .error (.terminal (.panic t)) ↔ ∃ n ls c' s' ch' ch'',
n + 1 ≤ fuel ∧ Prefix n … ls (c', s', ch') ∧ Finish … (.aborted t s' ch'') 1`; `= .error (.terminal .deadlock) ↔` a blocked endpoint at
`n ≤ fuel`; FUEL-OUT uses the NEGATION of `ZeroCost`, not of `Finish`: `= .error .fuelOut ↔ ∃ ls c' s' ch', Prefix fuel … ls (c', s', ch')
∧ ¬ ZeroCost c'` — the fixed tape's ACTUAL prefix of length exactly `fuel` with no zero-cost finish (an abort configuration at the
endpoint IS such a case). BOUNDARY CONTROLS, from the review's witness (`FuelBoundary.lean`, checked `scripts/capped lean`, exit 0):
`abort? = some _` → `execStmtLoop 0 = .error .fuelOut` and `execStmtLoop 1 = .error (.terminal (.panic …))`; `.next .stop` at fuel 0 →
`.ok`; a blocked form at fuel 0 → `.error (.terminal .deadlock)`; a renderer refusal at fuel 1 → `.error (.refusal r)`, at fuel 0 →
`.fuelOut`. `Prefix`'s refl/composition/splitting/erasure-to-`Steps`/exact-`stepFnIter`-agreement hold for every `n`, independent of
termination, so earlier labels survive fuel-out and divergence. **(4)** replay by RECORD: every consultation is a `consumeAtE site bound
ch` with its `PickRecord` (bound ≤ 1 → no record; empty tape → pick 0; modulo selection as `Choices.consume`); COVERAGE: `stepFn ctx s c
ch = .ok (c', s', ch', l) → ∀ ch₂, replays l.picks ch₂ ch₂' → stepFn ctx s c ch₂ = .ok (c', s', ch₂', l)` — no unrecorded consultation
affects a step; fixed-tape soundness/completeness (`stepFn_sound`/`step_complete` relabelled) + the witness direction for arbitrary
legal steps. **(5)** refusal SEPARATE: the unconditional `execStmtLoop fuel s c ch = r ↔ r ∈ {ok, terminal, fuelOut, refusal}` classified
by `Prefix`/`Finish`/a refusing `stepFn` call — four DISJOINT cases, no «all executions succeed» premise; THEN the corollary under a
proved reachable-state domain invariant (`step_preserves_wf` + what we can prove of no-refusal for the reached fragment); discharging
the domain facts for a source fragment stays theirs (§2 (5): «Our fragment rules will discharge the appropriate domain facts»).

Program level (one composable account): `runProgramSetupM … = .ok (pctx, c₀, s₀, locs, ch₁)` is the premise (setup's tape `ch → ch₁`
INCLUDED); readout `loadMany pctx sf locs`; output = the `out` fold. **`initPrintRefusal?` scope** ([AGENT], PENDING): the bridge covers
setup's choice consumption and states that init OUTPUT is empty BY REFUSAL (`runInitConfig` throws on `printOut?`) — the named
limitation is RETAINED in this window, not lifted (§3: «otherwise retain the named limitation»). Single-goroutine EMBEDDING first:
`execProgLoop_single`/`seqOpCount` restated over `StepLabel` with a PROVED cost or stuttering relation — never «equal fuel» asserted.
**The pool half WAITS for**: the labelled pool relation over `StepLabel` with attribution and terminal events (`program_run_iff`,
`observation_iff` relabelled), registry boundaries, pool deadlock's own condition — after the window (§2: «need not block this window»).
**THE LIMITS, stated in the offer and in any CLAUDE.md edit** (review): the program bridge ASSUMES successful setup, RETAINS the
init-print refusal, DEFERS pool/registry coverage; the restricted sequential result does NOT discharge the whole owed simulation.

## 3. Owed exposures by module

| Module | Laws / equations owed | Cite | Priority |
|---|---|---|---|
| Control, calls, defer (`Machine.lean`, `StepFn.lean`) | final method resolution + receiver entry (`enterFrame`/`enterFramePick`), parameter/result/capture layout, `pushDefer` registration and draining, `stepFrameExit`, return, panic/`recover` boundary (`recoverResult`), `seqCont`; per-arm `stepFn` equations over a SYMBOLIC continuation/environment/state with explicit operation premises; a NAMED rewrite set / `simp only` examples, no global unfolding | §4 P, §6 bullets 1, 5; §7 Q5 | 1 |
| Memory (`Ops.lean`: `loadLoc`, `storeLoc`, `Store.alloc`, `normalizeValueForTy`) | the allocation-NORMALIZATION premise stated; read/write/frame/freshness laws; initialization/preservation lemmas + LOCAL operation premises from which the logic maintains its invariant — no unexplained global well-formedness assumption per client; later: header/backing/sublocation/disjoint-update relations for slice borrowing | §4 C1, §6 bullet 4 | 2 |
| Blocks (C4) | block layout/allocation, lookup preservation, zero-value/type normalization, freshness/frame lemmas | §4 C4 | 2 |
| Choices (`State.lean`: `consumeAtE`) | replay/projection laws (`consumeAtE_fst_snd`, `_le_one`, `_of_lt` exist); exact per-step and terminal consultation coverage; the `repanicCollapse` terminal draw | §6 bullet 3 | 1 (with row 2) |
| Prefix/terminal/output (`Trace.lean`, `ProgramTrace.lean`, `MultiSound.lean`) | `iter_iff_trace`, `Trace.erase`, `run_ok_iff` relabelled; composition/erasure/executable correspondence; `ZeroCost`, `Finish` with cost, the fuel-out theorem; terminal classification, rendering/consumption, output projection; `runProgramM`/`runProgramPoolOutM` setup/readout composition + the cost/stuttering correspondence | §6 bullets 1–2; F2 | 1 |
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
- **NaN** — DEFERRED ([USER]); BUG-094's plan stands without a lane; its fidelity debt remains (review). **Typed profiles** — PARKED
  ([USER] 2026-09-16). **No `Language` spike** — DROPPED (proposal §2; endorsed §7 Q8). **The pool/registry half** — after the window
  (§2). **Corrected reading** (§1): the logic's live backend is the refusal-observing `Safe` adapter, not `adequate_program_result` — the
  proposal's O-CLOSE premise reading is superseded; our (5) serves their universal refusal exclusion by making refusal a reported case.

## 6. Sequencing and lanes

- PARALLEL: row 0 ‖ E6a (records touch `docs/`, `GoLean/GoCore/BridgeSet.lean`; E6 touches the frontend, decoder, `Corpus/`, baselines).
  Corpus lanes (§4) ‖ the core lane whenever files do not overlap (`Corpus/`, `baselines/`, ledgers vs `GoLean/GoCore/`).
- E6a → E6b → E6c → E6d → E6e SERIAL (one frontend writer: all touch `tools/nativefrontend/unseq.go` + the decoder); E6e only at a
  census that is zero on BOTH sweeps with the preservation evidence in hand — if a slice is REFUSED by the [USER], E6e does not run
  and the triple stays (flagged at that gate; the window continues with row 2, the retirement moving to a later window under a new ruling).
- ONE CORE WRITER: `GoLean/GoCore/` has one lane at a time — rows 2 → 3 → 4 → 5 → 6 SERIAL (B6 → C4 serial per §Recommendation; the
  proposal's B6 ‖ C4 slot is withdrawn). `BridgeSet.lean` is row 0's until row 2 opens, then the core lane's; it is re-pinned per row.
- Row 2 is ONE candidate: the reshape lane lands first internally, Codex forks from its tip; they merge together (their §Recommendation).
- PER ITEM: the merge protocol exactly (`CLAUDE.md`) — gate green (class per row), the audit ask, at-that-moment sign-off, `--ff-only`,
  step 5a re-certification; a PASS→non-PASS flip needs a `BUGS.md` Cases line; every design gate (G-P, G-C3, G-C4) is a HARD STOP.
- ONE re-pin at close (row 7); NOTHING reaches the customer before it; no interim pin, no calendar deadline (§7 Q10).
- SESSIONS [AGENT estimate; precedents B7 one, C1 three + audits, `unseq` stages one each]: ≈ 24–37 serial, ≈ 20–30 with the parallel
  lanes (rev. 1's 20–30 grew by E6's accounting, +4–7; the proposal's 13–17 by the five corrections, the coverage theorem, the equations
  and the C4 audit).

## 7. Decisions for the [USER] (each PENDING; provenance [AGENT] proposal unless marked)

1. APPROVE this charter (rev. 2) as the window of record (the order, contents, conditions and exposures of §1–§3).
2. AUTHORIZE the records/contract lane NOW (row 0; their §7 Q7 «Now for the contract and inventory»; the F3 inventory procedure).
3. LAND this documentation branch (`docs/roadmap-customer-alignment-0922`) together with the review branch: audit trim or WAIVER for a
   docs-only branch (posed 2026-09-23).
4. DISPATCH E6 as the window's first item (row 1; ruled 2026-09-22 as a lane, placed here by the addendum + their Q2), starting with E6a.
5. The E6 SPLIT (F1): approve the five slices E6a–E6e and their exit — each of E6b/E6c/E6d is a grammar widening POSED here, none
   authorized by the review; the exit stays whole-corpus + twin zero WITH preservation evidence; the estimate 6–10 (was 2–3).
6. Codex for the statement/bridges lane (row 2's closure, coverage and bridges; row 7's equations) as a separated lane forking from the reshape.
7. Dry-run ACCESS: a gitignored isolated clone of their tip under `deps/` at the offer (row 7) — evidence only; else the offer goes without it.
8. The «independent in-repo consumer» (their §6): read as a TOY semantic-equation CLIENT — GoCore only, symbolic state/continuations,
   using the supported equations, in the test/contract graph with exhaustive enrollment and no runtime dependency — NOT an Iris
   `Language` instance (PARKED 2026-09-16; CLAUDE.md's «we DO NOT ship any higher level reasoning» stands). Confirm.
9. C4's preservation claim: adopt their SCOPED form (injection + stuttering over a stated observable domain, escape audit first) as a
   REFINEMENT of the G-C4 caveat's statement, the behavioural gate unchanged — the gate is re-posed when reached.
10. `initPrintRefusal?` — RETAIN the named limitation through the window (§2 above); lifting it is a later item.
11. CLAUDE.md's owed-simulation sentence («terminal priority») will need the `Prefix`/`Finish` wording AND the stated limits (§2 tail) at
    landing — a CLAUDE.md edit, [USER]-approved; it must not mark the owed simulation discharged.

**Landing record ([AGENT] coordinator, 2026-09-24).** This charter (rev. 2), the proposal, the logic team's response, the
Codex review and the rulings landed on `main` at `3fb4a0d1` (train r48, documentation only): pre-merge main `9269912e` →
`refs/snapshots/r48/main`; `release-check` «No certification inputs/claims changed»; `GOLEAN_MEM_MAX=48G scripts/capped
scripts/ci` EXIT=0 in 413 s, `RESULT: PASS`; the adversarial audit WAIVED for this docs-only landing by [USER] ruling 3
(2026-09-24). The window is open: E6a and the fixture inventory dispatched; Codex packet A's brief in preparation.
