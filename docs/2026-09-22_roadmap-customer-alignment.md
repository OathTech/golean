# Roadmap vs the customer's proofs — an alignment memo (2026-09-22, rev. 2)

[AGENT] analysis worker, lane `docs/roadmap-customer-alignment-0922` (off main `92234a6f`). Records only: no code, no
gate, no baseline. Every recommendation is [AGENT]; every decision PENDING [USER]. Claims about the customer cite a
file/theorem/lesson or are marked **[inf]** (this worker's inference). Rev. 2 (same day) surveys the customer repo the
[USER] named after rev. 1: `/home/dev/projects/golean-logic/` (git, main `5801c71`, origin `OathTech/golean-logic`),
READ-ONLY — nothing there was modified, built or run. Paths `L:…` below are relative to that repo; `G:…` to this one.

**The question** ([USER] Mike, 2026-09-22, verbatim, relayed by the [AGENT] coordinator — cite as relayed): «Our ultimate
aim here is to support the GoLean logic that we're building in a different repo. That's our upstream customer. Which of
the things that we're building are actually useful for those customer proofs and is our prioritization right?». This
revises the 2026-09-11 «we don't have as of now a customer» ruling; the 2026-09-16 «what this repo provides» statement
(`G:CLAUDE.md`) and the F10 boundary (relation + coherence here; Iris resources/WP/proofs downstream) stand and are assumed.

## 0. The customer, first-order (rev. 2) — and the proxies rev. 1 used

| Fact | Evidence |
|---|---|
| **Pin**: GoLean `61958f2e` = «Train r39 close … B7 landed» (2026-09-17); vendored as an exact ignored clone `.golean-ws/` consumed by a relative Lake `path` dependency; Iris `e7a0a43`, Lean 4.32.2 | `L:provenance/pins.json` (`golean.rev`), `L:packages/golean-iris/lakefile.toml`, `L:docs/2026-09-17_architecture.md` «Vendored semantics workspace» (modelled on `cerberus-sl`'s `.cerberus-ws`) |
| **Distance**: 92 commits behind main `9269912e`. HAS B4/C5, C2, B7, `unseq` Stage B. LACKS C1 (S0–S3: the `AccessTrace` label, the table deletion, `Store.alloc` normalization), BUG-111 canonical-path keys, `unseq` Stages C/D/E/E5 (trains r41–r47) | `git rev-list --count`; at the pin `Step : Config → Store → Config → Store → Prop` (`G:Machine.lean:4390` @pin), `stepFn … : Except Stop (Config × Store × Choices)` (`G:StepFn.lean:255` @pin) vs main `… × AccessTrace` (`G:StepFn.lean:327`) |
| **Re-pin protocol**: none automated; «Any required semantics change is an upstream task with an isolated checkout and an explicit pin review»; «Pins remain fixed unless actual upstream missing support requires a separately recorded change» | `L:docs/2026-09-19_f1-design.md:28-31`, `L:docs/2026-09-20_e1-design.md:110-112`; every landing since 09-17 says «Pins are unchanged» (`L:docs/2026-09-17_claim-ledger.md`) |
| **What it imports**: `GoLean.GoCore.Multi` ×9, `Syntax` ×4, `Trace` ×3, `State` ×1, `MultiSound` ×1 — no `Interface`, no `MachineSound` directly | `grep '^import GoLean'` over `L:packages/`, `L:examples/`, `L:consumers/` |
| **What it names** (occurrences): `stepFn` 92, `ProgramCtx` 117, `Store` 106, `Config.` 59, `runProgram*` 59, `Choices` 54, `Cont.` 48, `execStmtLoop` 24, `recoverResult` 15, `stepFn_sound` 15, `seqCont`/`enterFrame`/`pushDefer` 10 each, `stepFrameExit` 5, `step_complete` 4, `Steps` 4, `run_ok_iff` 1; **zero**: `AccessTrace`, `StateWf` (1), `step_preserves_wf`, `stepFn_consumption*`, `StepEvent`, `MultiConfig`, `unseq`, `mapRange`, `Platform` | identifier census over the same trees; all 33 named GoLean declarations still exist on main (`G:` grep) — the re-pin delta is the 4-tuple/label, not renames |
| **Subjects**: Boolean/uint64/pointer scalars, one-field structs, `map[uint64]uint64` get/comma-ok/store, direct nonrecursive calls, closures capturing by address, `defer`, `panic`/`recover` (F0-era, «a separate future extension» in the calculus). No goroutines, channels, `select`, `range`, slices, floats, `unseq` | `L:examples/fixtures/{f1,e1,callchain,shared,recovery,error-string}/main.go`; `L:…/Logic/Source.lean` `ScalarTy = boolean | pointer | word64 | recordPointer | map`; `L:…/Data/Record.lean` («one-field record schemas»); next: F2 cleanup, E2 «bounded byte reads», multi-field records, the raft `recvAck` method (`L:docs/2026-09-18_master-plan.md` §6) |
| **Rev.-1 proxies** (park `proofs/`, `spikes/iris-customer`) | both dead against main by the C-arc's refactors; the live customer is the third generation and consumed the SAME shapes — `Trace.lean`'s bridge, `stepFn` equations, whole-root `gen_heap`, CPS over `Cont` |

## A. What a GoCore program logic needs — status, now checked against what the customer BUILT

| # | Requirement | Status | Where / what the customer did with it |
|---|---|---|---|
| 1 | Step relation with values, `val_stuck` | SATISFIED | `ContextExpr ctx := {config}` over `Step ctx`, `Obs := Empty`, `Val := Unit`, forks `[]` (`L:…/Language.lean`); F0 adds `Safe.Expr := run Config \| fault` with a `refusal` transition on `stepFn … = .error` so `NotStuck` excludes EVERY refusing tape (`L:…/Logic/Language.lean` «choice-uniform executable definedness») |
| 2 | Fork list / pool | SATISFIED (spawn) / PARTIAL (pairing) | unused: the customer is sequential through F4 (`L:docs/2026-09-18_master-plan.md` §6) |
| 3 | Evaluation contexts + bind (`Language.Context`) | MISSING — **and deliberately not wanted as a fill law** | bind is a CPS triple over the REAL continuation: `Kernel.Triple P Q start := □ ∀ k Φ, P -∗ (Q -∗ WP (.next k)) -∗ WP (start k)` (`L:…/Logic/Kernel.lean`); two exits `.next k` / `.signal .ret k` (`L:…/Logic/SourceKernel.lean` `Control`); `Control.Agrees : List Authority → Cont → Prop` relates their pending-defer authorities to the spine `.stop \| .seq \| .frame` — «Other control constructs require new agreement lemmas» (`L:…/Logic/Control.lean`). Their obligations REJECT «Arbitrary context-fill bind» (recover vs helper counterexample; `L:docs/2026-09-18_logic-obligations.md` §4 row 1; `…_logic-interface-draft.md` §4 E-BIND, §9) — cerberus L4's hand-proved bind, chosen on purpose |
| 4 | A heap-only state | SATISFIED | `Store` is exactly what they interpret (`heapToMap : Heap → ExtTreeMap Nat HeapCell`, `L:…/Heap.lean`); B7's `ProgramCtx` is their expression INDEX («a transition can update only `Store`; it cannot switch this index») |
| 5 | Points-to granularity | PARTIAL — sufficient for them today | «this first customer owns a whole root cell, not disjoint fields of one cell» (`L:…/Heap.lean`); «Whole-object ownership remains an acceptable first policy for richer records» (master plan §6); `AccessTrace` unused. E1's map ownership models our B1 entry-identity stamps («Entries retain their identities on replacement and receive the counter's fresh identity on insertion», `L:…/Data/WordMap.lean`) — a re-pin past BUG-111 (r42) touches this **[inf]** |
| 6 | Executable ↔ relation coherence | SATISFIED | load-bearing: `stepFn_sound` ×15, `step_complete` ×4 (`pure_of_stepFn`, `step_unique`, `L:…/Lifting.lean`) |
| 7 | Determinism where nothing is consumed | PARTIAL on our side; SOLVED by them | every rule's premise is a UNIVERSAL equation `∀ state choices, stepFn ctx state c choices = .ok (c', state, choices)` + `step_complete` ⇒ unique successor (`step_unique`). Cost: 92 `stepFn` unfoldings; «plain `rfl` did not unfold enough … `cbv` exceeded its heartbeat budget on the full artifact … `with_unfolding_all rfl`»; a «noncompiled sizeOf helper» upstream had to be replaced (`L:docs/2026-09-19_execution-log.md:309-313`) |
| 8 | Fuel-free relation; end-to-end bridge | SATISFIED (seq, via OUR `Trace.lean`) / PARTIAL (program, pool) | `adequate_execStmtLoop` is proved from `Semantics.run_ok_iff` + `Trace.erase` (`L:…/Adequacy.lean:71-76`) — `G:Trace.lean` IS consumed; F0's version covers all fuel/tapes with `RunProperty: ok→φ, fuelOut→True, other error→False` (`L:…/Logic/Language.lean:147-154`). Program level: `adequate_program_result` needs `seqOpCount … = 0` (zero registry boundaries) and a successful `execStmtLoop` premise; output is `∃ out` (`L:…/Readout.lean`). Their ledger: «does not provide a general labelled I/O simulation or arbitrary concurrent-pool adequacy theorem. The upstream end-to-end simulation obligation is not discharged by this layer» (`L:docs/2026-09-17_claim-ledger.md`) |
| 9 | Panic/`recover` discipline | PARTIAL | they name `recoverResult`/`recoverThroughWrappers`/`markNewestRecovered` and the seven `CallSite` entry shapes incl. `deferPanic` (`L:…/Call.lean`, `Unwind.lean`); `Func.wrapper` is a premise (`hw : f.wrapper = false`, `L:…/Logic/Control.lean` `entry_step`; the `w` slot of every `.frame`) |
| 10 | Picks/output as observations | SATISFIED (pool) / MISSING (seq) | their `Obs := Empty`; O-TRACE («Empty observations and heap ownership do not supply this») and A-TRACE are THEIR later obligations for Raft (`L:docs/2026-09-18_logic-obligations.md` §2 O-TRACE) — the shape they will need from us is a per-step event (`G:Multi.lean:1009` `StepEvent.out`) reachable from the SEQUENTIAL relation |
| 11 | Init in the statement | PARTIAL → they did it | `ProgramExecution.setup` discharges `runProgramSetupM` for their fragment (globals `#[]`, no `$pkginit`, reserved prefix) (`L:…/Logic/ProgramSetup.lean`) |
| 12 | Refusal/domain boundary | PARTIAL → they did it | F0's `fault` transition + `Source` admission (structural, «not a successful-execution certificate», `L:…/Logic/Source.lean`); typed profiles stay parked — confirmed by their boundary table: «core `Admission*` checker … remain upstream; the Boolean/recovery profiles and old facade belong downstream» (`L:docs/2026-09-17_master-plan.md` §2) |
| 13 | Terminal classification (abort ≠ refusal) | MISSING as a statement | O-TERMINAL: «Uncaught panic is a terminal classification without a successful sequential successor. It is not a value of today's Iris adapter» (`L:…_logic-obligations.md` §1/§2) — the «terminal priority» component of our owed simulation is exactly this |
| 14 | Stable boundary + pin | MISSING as a contract; their side is a vendored clone + `pins.json` | they want no re-export module; they unfold `stepFn`. What makes THEIR re-pin cheap: stable bridge names (`run_ok_iff`, `Trace.erase`, `execProgLoop_single`, `execProgLoopOut_snd`, `runProgramSetupM`, `loadMany`) and a per-pin changelog of changed `stepFn` arms **[inf]** |
| 15 | Reduction to Go's access granularity | MISSING | irrelevant to them before F4/Raft («Concurrent Node, network/storage models and system liveness are separate extensions», obligations §6) |
| 16 | Platform parametricity | PARTIAL | «The platform is the pinned GoLean default (gc, linux/amd64), not a new portability contract» (claim ledger) — 0 uses |

Discussion. Rev. 1's MISSING cluster was «the bind law and the end-to-end statement». The live customer has SOLVED bind for
itself by CPS over the real `Cont` and REJECTS a fill law on Go grounds (recover), so row 3 falls from the critical path; it
has BUILT the sequential half of row 8 on top of our `Trace.lean` and needs from us only the parts it says it lacks: the
terminal classification (13), observations (10) and the pool/registry bridge (8) — i.e. the STATEMENT of the owed
simulation, not a re-proof of what they have. Its dominant cost is unfolding `stepFn` per arm (row 7), which is exactly
what every C-arc reshape re-prices: since 2026-09-17 they are a pinned two-repo consumer, and the plan's own warning
(`G:docs/2026-09-04_reasoning-surface-plan.md` §5.1: «the LAST time this reshaping is cheap») has already come due.

## B. Each roadmap item, re-valued against the live customer

Cost precedents unchanged from rev. 1 (B7 one session; C1 ~3 + audits; `unseq` ~1/stage; plan §5.1: P 3–4, C3 3–4, C4 2+re-pin, B6 2–3).
«Re-pin cost» = what the customer pays when it next moves its pin across the item (their 92 `stepFn` sites, `CallSite`, `Agrees`, `Frame.roots` address arithmetic).

| Item | CUSTOMER value | Re-pin cost to them | FIDELITY | Cost (us) | [AGENT] recommendation |
|---|---|---|---|---|---|
| E6 (trigger; non-main grammar + twin re-pin; legacy triple retirement) | L — `unseq` 0 uses; their 13 fixtures are single-call statements with local targets or call-free comma-ok lookups, so none should enter a graph at main **[inf — verify by lowering their fixture SHAPES with main's frontend, GoLean-side]** | L (one `Cont` frame fewer) | H | ~2 | do now (dispatched) |
| Two decoder follow-ups; status-diverse manifest row | L | 0 | M | ≤ 1 | ride E6 / next apparatus lane |
| NaN [a]+[b] (BUG-094) | **0** — floats are outside `ScalarTy`; no fixture has one | 0 | M–H | 1–2 | a pure fidelity call: keep the [USER]'s 2026-09-19 slot (after E6) or defer — no customer stake either way (rev. 1's «defer» withdrawn) |
| P (native method promotion) | L now, M later (E2's pointer-receiver method) | **H** — deletes `Func.wrapper` (their `entry_step` premise, every `.frame … w`, `FrameRecovery`) | M | 3–4 | do, but ONLY inside the batched re-pin window (§D-4) |
| C3 (`Cont := List Frame`) | **M** (was H) — their `Agrees`/`pushDefer`/`Cont.rebuild_*` lemmas become list induction; not a blocker (bind is CPS) | M — patterns survive via `@[match_pattern]` views; `stepFn` unfoldings re-elaborate | L | 3–4 | keep; batch (§D-4); stop calling it the bind prerequisite |
| C4 (block-scoped allocation) | L–M — fixed `.seq` envs simplify `Control.Agrees .seq` | **H** — `Frame.roots base n`, `initialCells`, `declareRoots` compute `Loc.base` ids from allocation ORDER (`L:…/Logic/Readback.lean`, `Call.lean`) | L | 2 + re-pin | batch; disclose the address shift in the changelog |
| B6 (`VarId := Nat`) | L–M | **H** — `Source.Context.lookup` by spelling, `LocalEnv.declare name …` (`L:…/Logic/Source.lean`, `Binding.lean`) | L | 2–3 | batch |
| The owed labelled simulation | **H** — precisely their O-TERMINAL / O-TRACE / registry gaps (A-8, 10, 13); the sequential part exists on both sides | 0 (additive) | L | statement note 1; terminal + output components 1–2; pool half 2 **[inf]** | DO NOW: the statement note; the pool half when they reach E2/F4 |
| Typed-profile invariants (parked) | 0 — their boundary table puts profiles downstream | — | L | — | stay parked (confirmed) |
| Interface facade + pin protocol | **M–H, in a DIFFERENT form**: not a re-export module (they import `GoCore.*` and unfold `stepFn`) but (i) stable bridge names, (ii) a per-pin changelog of changed arms/shapes, (iii) optionally per-arm `stepFn` equation lemmas as a supported `simp` surface (their heartbeat pain, A-7) | — | L | (i)+(ii) 1; (iii) 2 **[inf]** | write the `61958f2e → main` changelog NOW (it is also the re-pin rehearsal); (iii) PENDING [USER] |
| Fidelity lanes generally | M where their features are: scalars, pointers, one-field→multi-field structs, `map[uint64]…` get/set/comma-ok, direct calls, closures-by-address, defer, panic/recover; E2 adds byte slices + pointer-receiver methods | — | H | ongoing | weight the corpus toward that list; `unseq`/floats/concurrency rows carry no customer weight until F4 |
| Reduction to Go's access granularity (NPDRF) | 0 until Raft/F4 | — | L | VERY H | restate-only (design note), unchanged |
| A `Language`-instance spike | **L** (was H) — their adapter answers the shape questions (`Obs := Empty`, `Val := Unit`, refusal → `fault`, no fill); what remains open is OUR label/terminal shape, which the simulation note decides | — | 0 | — | DROP as a GoLean spike; read their `Language.lean` instead |
| `unseq` DRF-confluence lemma (rev. 1 §C-1) | 0 now; M at F4 («general `unseq` … not first-slice coverage», draft §8) | 0 | L | 2–3 | DEFER; keep owed |

## C. What the roadmap is missing that THIS customer needs (rev. 2)

| # | Gap | Evidence | [AGENT] |
|---|---|---|---|
| 1 | A statement with terminal classification: abort (`Config.abort?`) vs refusal vs fuel, for the sequential driver and the pool | O-TERMINAL; `RunProperty` treats every non-fuel error as `False` — they cannot state a permitted-panic theorem | in the simulation note (§D-2) |
| 2 | Output (and picks) observable from the sequential relation, not only `StepEvent` at the pool | O-TRACE/A-TRACE; `∃ out` in `adequate_program_result`; Raft needs `Ready.CommittedEntries` observations | a `Step` label of `access ⊕ pick ⊕ out` **or** a sequential projection of `StepEvent`; decide BEFORE the batched re-pin (PENDING [USER]) |
| 3 | A program-level bridge without the `.ok` premise and without `seqOpCount = 0` | `L:…/Readout.lean` premises; their F0 `Safe` loop theorem shows the shape | the pool half of the simulation, timed to E2/F4 |
| 4 | A re-pin changelog `61958f2e → main` (stepFn 4-tuple, `Step` label, `Store.alloc` normalization, BUG-111 keys, Stage C–E5 lowering triggers, the born choice sites) | they hold the pin until «actual upstream missing support» forces a move; nothing on our side tells them what moved | 1 session, now |
| 5 | Per-arm `stepFn` equations / a supported `simp` set | A-7's heartbeat evidence; 92 unfold sites | PENDING [USER] |
| 6 | Batching the remaining breaking reshapes (C3, P, B6, C4, the label) into ONE window | each is a two-repo change now; four separate windows = four re-proofs of the same 92 sites | §D-4 |

## D. Proposed sequence (all [AGENT]; each reorder PENDING [USER])

1. **E6 as dispatched** (~2 sessions, one core writer) — unchanged; verify GoLean-side that the customer's fixture shapes do not enter a graph.
2. **Now, records lane (1–2 sessions):** the re-pin changelog `61958f2e → main` (C-4) **and** the labelled-simulation STATEMENT note with its terminal/observation components (C-1, C-2), posing the `Step` label shape as a [USER] decision.
3. **NaN** at the [USER]'s slot (no customer stake) — or after 4 if the [USER] prefers; ~1–2 sessions.
4. **One batched breaking window**: the label change (if ruled) → C3 → P → B6 ‖ C4, each gated as today, then ONE re-pin offer with the changelog. ~10–13 sessions total; the customer re-proves its 92 sites once.
5. **The pool/registry half of the simulation** when the customer reaches E2/F4 (their `recvAck` and observation work); the `unseq` confluence lemma and NPDRF restatement stay owed, not scheduled.
DROPPED vs rev. 1: the GoLean-side `Language` spike (their adapter is the answer); «C3 first» (bind is not their blocker). DEFERRED: the confluence lemma. UNCHANGED vs today's plan: E6 first; NaN's slot is the [USER]'s; NPDRF restate-only; typed profiles parked.

**PENDING [USER] questions, in priority order.**
1. Re-pin cadence: batch C3/P/B6/C4 (+ the label) into one window with a changelog and a single re-pin offer (§D-4), or land them as they come and let the customer absorb each? [AGENT]: batch.
2. The sequential `Step`/`stepFn` label: memory-only (today) vs `access ⊕ pick ⊕ out` — their O-TRACE needs output observable; decide before the batch (§C-2).
3. Authorize the records lane now: the `61958f2e → main` changelog + the simulation statement note (§D-2).
4. Is the «interface» for this customer stable bridge names + a changelog (+ optionally per-arm `stepFn` equation lemmas, §C-5) rather than a re-export module? [AGENT]: yes; (iii) is optional.
5. NaN timing — a fidelity-only call; no customer stake.
6. Confirm: no GoLean-side `Language` spike; the pool half of the simulation waits for E2/F4; NPDRF restate-only.
7. Whether to weight the differential corpus toward the customer's feature list (§B fidelity row) — e.g. multi-field structs, byte slices, pointer-receiver methods ahead of the E-family widenings.
