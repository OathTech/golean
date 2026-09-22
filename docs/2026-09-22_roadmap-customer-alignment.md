# Roadmap vs the customer's proofs — an alignment memo (2026-09-22)

[AGENT] analysis worker, lane `docs/roadmap-customer-alignment-0922` (off main `92234a6f`). Records only: no code, no
gate, no baseline. Every recommendation here is [AGENT]; every decision is PENDING [USER]. Claims about what the
customer needs cite a file/theorem/lesson or are marked **[inf]** (this worker's inference).

**The question** ([USER] Mike, 2026-09-22, verbatim, relayed by the [AGENT] coordinator — cite as relayed): «Our ultimate
aim here is to support the GoLean logic that we're building in a different repo. That's our upstream customer. Which of
the things that we're building are actually useful for those customer proofs and is our prioritization right?». This
revises the 2026-09-11 «we don't have as of now a customer» ruling (`docs/2026-09-11_review-dispositions.md`); the
2026-09-16 «what this repo provides» statement (`CLAUDE.md`) and the F10 boundary (relation + coherence here; Iris
resources/WP/proofs downstream; a thin adapter SPIKE permitted in-repo) stand and are assumed below.

## 0. Who the customer is, as far as this repo can see

| Proxy | What it is | What it consumed from us | Staleness |
|---|---|---|---|
| `park/reasoning-2026-08-31` `proofs/` (`7440bf70`) | the full Iris layer: `Lang.lean` (bare `Language` over `Step`), `LangC`/`LangD` (pool: spawn lift; pairing DECOMPOSED per thread), `Adequacy`, `Lifting.wp_store_step`, `HeapBridge` (whole-cell `gen_heap` keyed by `Addr`), `Laws/Bind.wp_plug_bind` (hand-proved bind with `hdrain`) | imports: `GoCore.Syntax` ×33, `MachineSound` ×29, `StepFn` ×5, `MultiStreams` ×5, `MultiSound` ×4, `NativeToIR` ×2, `SyntaxEqb` ×2, `Value/State/Ops/Multi/MachineEqb` ×1 (`git grep` on the branch) | dead against main: `ExecState` → `ProgramCtx × Store` (B7), `Heap` list → `Array HeapCell` (A2), `Step` now 5-ary with an `AccessTrace` label (C1), `.panicked` gone (B4), `coerceStoredValue`/`typeResolutionFuel` gone (C2) — archaeology §6 |
| `spikes/iris-customer` @ tag `typed-profiles/last-main-2026-09-16` | the September adapter: dense-cell `gen_heap`, `wp_call` over seven entry shapes, shared-capture recovery fixture, all-choice results through the shipped driver (archaeology §6 «The current customer») | `import GoLean.Interface` ×9, `GoLean.NativeToIR` ×1 | `GoLean/Interface.lean` DELETED 2026-09-16 (`docs/2026-09-16_typed-profiles-parked.md`); the spike no longer builds |
| `deps/iris-lean` @ `e7a0a43` | the logic's substrate: `Language`/`Context`/`EctxLanguage`/`StateInterp`/`adequate` (`Iris/ProgramLogic/{Language,EctxLanguage,WeakestPre,Adequacy}.lean`) | — | the pin both proxies used |
| `deps/reasoning-revival/raft-proofs/` (git repo, origin `OathTech/raft-proofs`, tip `67d9b68`) | NOT the logic. A Lean-only Verdi port + etcd-raft executable mirror; **zero `import GoLean`** lines; its docs name «External reasoning repository … Customer of GoLean; not implemented inside the Raft proof packages» and «GoLean … Consumed by pin; other agents own its ongoing work» (`docs/2026-09-16_master-plan.md` §1 table); pin alias G = GoLean `32398203` (2026-09-16, on main) | nothing yet; intends `packages/etcd-raft` → «pinned GoLean semantics/interface» + the external logic (`docs/2026-09-16_architecture.md`) | a SECOND-ORDER customer; its shape requirements (§A rows 8, 11, 13) are still evidence |

No checkout of the logic itself exists under `deps/` (searched 2026-09-22). **The park and the spike are the only
first-order evidence; both are stale by exactly the refactors the C-arc made — which is itself the strongest datum: the
customer's cost is our API's motion, and a pin/interface record (§C-5) is what converts motion into a dated re-pin.**

## A. What a GoCore program logic needs from the semantics

| # | Requirement (source) | Status | Where it is / what is missing |
|---|---|---|---|
| 1 | A step relation with values, `val_stuck` (`Language`, iris `Language.lean`; park `Lang.lean` `toVal ⟨.next .stop⟩ = some ()`) | SATISFIED | `Step : Config → Store → Config → Store → AccessTrace → Prop` (`Machine.lean:5315`); the value shape unchanged since the park; rule multiplicity = demonic nondeterminism (plan §1.4) |
| 2 | A fork list per step (`primStep … → Expr × State × List Expr`) | SATISFIED (spawn) / PARTIAL (pairing) | `StepE : Nat → … → List Config → AccessTrace → Prop` (`Multi.lean:2084`) is iris-shaped; `StepM` pairing/wake touch TWO threads in one step (`:2124`) — the park's `LangD` decomposition was the customer's proof-layer work and stays theirs (plan §1.14) |
| 3 | Evaluation contexts + bind (`Language.Context`: `primStep_fill`/`_inv`; `EctxLanguage.fill`) — cerberus L4 | MISSING | no `fill` in `Machine.lean` (a docstring mention at `:3782` only); `recoverResult` reads `k` (`:3763`); the two-step abort that forced the park's `hdrain` is gone (B4), but the abort `.panicking chain .stop` STEPS under `fill K` while `c` does not — `primStep_fill_inv` fails at the abort unless the abort is value-like **[inf]**; plan §1.7's 2026-09-05 annotation: REJECTED as sketched, owed to a spike |
| 4 | A state the interpretation can own (`StateInterp State …`); heaplang: heap only | SATISFIED | `Store = {heap}` (`Store.lean`, B7); `ProgramCtx` a section variable — L11's three pin equalities gone; `Store.allocCell` deterministic (`nextAddr = size`) — L8's one-rule alloc |
| 5 | Points-to granularity: per-field/leaf keys + the frame rule's disjointness = the detector's overlap (plan §1.14(3), L7) | PARTIAL | root cells + path-addressed leaf ops (C1 D1(a)); `ShadowKey` overlap table (`Race.lean`); mover lemmas `storeLoc_root_frame`, `loadLoc_after_disjoint_store` (`NPDRF.lean`), `Mem.store_congr`/`loadLoc_root_congr` (`MachineSound.lean:3470/:2783`); no `Store.toKeyMap`, no leaf-keyed `genHeap_update` bridge — the customer's G-REPR |
| 6 | Executable ↔ relation coherence, both directions (L3) | SATISFIED per step | `stepFn_sound` `:1681`, `step_complete` `:2079` (`MachineSound.lean`); `stepMulti_sound` `:1188`, `stepM_complete` `:1334`, `execProg_single_eq_execStmt` `:822` (`MultiSound.lean`) |
| 7 | Determinism where nothing is consumed (`step_det_of_choiceFree`, plan §1.4 G12) — turns «some run» into «every run» | PARTIAL | `stepFn_consumption_none/some` (`MachineSound.lean:5785/:6175`) + row 6 imply it; no named lemma; one-pick determinizations exist engine-side (`EnumDedupSound`, `MultiStreams.lean:527`) but are off the interface (plan §1.12) |
| 8 | Fuel-free relation; fuel exhaustion transparent (L1/L2); «finite prefixes, not a runner budget» (raft-proofs `2026-09-17_mirror-safety…` §3) | SATISFIED / end-to-end PARTIAL | `Steps` (`Machine.lean:6157`); `Trace.erase : Trace → Steps` (`Trace.lean:42`), `run_ok_iff` `:60`, `Pool.run_iff` (`PoolTrace.lean:79`), `program_run_iff`/`observation_iff`/`fuel_is_not_observation` (`ProgramTrace.lean:30/:79/:72`); the CONVERSE (relation run → some `fuel, ch` on the driver) needs the stream-composition theorem `Trace.lean`'s header names as missing = the owed labelled simulation (`CLAUDE.md` (2)) |
| 9 | Panic/`recover` frame discipline | PARTIAL | B4: one `.panicking` unwinding form, `Signal` table, no k-less abort; `pushDefer`/`recoverThroughWrappers` are continuation WALKS (`Machine.lean:3543`) — list ops after C3; the recover side condition of row 3 remains |
| 10 | Choice tape → what the customer quantifies over; picks as observations; fairness as a trace hypothesis (plan §1.14(1); latitude §11 item 6) | SATISFIED (pool) / PARTIAL (seq) | `StepEvent.{picks, out, trace}` (`Multi.lean:1009`) at the pool; the sequential `Step` label is `AccessTrace` ONLY — picks and `out` are not in it, so a sequential `Language` instance cannot put them in `obs` without re-deriving them **[inf]** |
| 11 | Output as events (G-OUT); raft-proofs wants observation-preserving refinement of `Ready.CommittedEntries` | SATISFIED (pool) | `StepEvent.out : List GoString`, folded by the drivers; `observation_iff` |
| 12 | Init as part of the statement (review §7; plan §1.14(4) `StateWf σ →`) | PARTIAL | `ProgramRun` (`ProgramTrace.lean`) carries `runProgramSetupM` as an EXECUTABLE premise («not a claimed typed-admission proof») |
| 13 | The refusal/domain boundary: which `Accepted` programs the relation is total on (L9; `adequate .NotStuck` treats a refusal as stuck) | PARTIAL | `StateWf` + `step_preserves_wf` (`StateWf.lean:8106`); `Admission.lean` is «experimental, deliberately small»; the typed profiles PARKED 2026-09-16; no `Accepted → refusal_free`; the partial-correctness boundary is stated in `CLAUDE.md` (2), which is honest and enough for a sequential WP that carries its own admission hypothesis (the spike did: `Admission.lean`) |
| 14 | A stable boundary + pin (L9/L10/L15) | MISSING | `GoLean/Interface.lean` deleted; the customer pins a SHA (raft-proofs alias G); `scripts/check-core-audit`'s 51 required theorems are the closest designated set; two proxies already drifted to death (§0) |
| 15 | Reduction to Go's access granularity (concurrent meaning of a machine-step logic) | MISSING | `NPDRFReduction` `@[deprecated … FALSE as stated]` (`NPDRF.lean:483`, [USER] 2026-09-18); `CLAUDE.md` (3): «an explicit open obligation, not a theorem» |
| 16 | Platform parametricity (`∀ p` vs `gcAmd64`, L11) | PARTIAL | `Platform` a global constant (B7 D1(a), [USER] 2026-09-16); theorems are at `gcAmd64` |

Discussion. Rows 1, 4, 6, 8 are the load-bearing ones and they are in better shape than at the park: the C-arc's B4/B7/C1/C2
removed exactly the pitfalls the cerberus lessons name (L1, L2, L6, L8, L11). What is MISSING clusters in two places — the
bind law (row 3, with rows 9/10 as its side conditions) and the end-to-end statement (row 8's converse, 12, 13, 14).
Neither is a fidelity item; neither moves a corpus row; both are what an adequacy theorem downstream consumes first
(plan §1.14(4): `go_adequacy … → ∀ fuel ch, run … ∈ {.ok r | φ r} ∪ {.fuelOut}`). Row 15 is the only concurrent-meaning
gap and is the most expensive thing in this table; the customer's own first subjects are sequential (the park's corpus;
raft-proofs «sequential RawNode ownership»), so it is not on the critical path **[inf]**.

## B. Each roadmap item: customer value vs fidelity value vs cost

Cost precedents: B7 S0–S5 in ONE session (`docs/2026-09-17_b7-context-store-handoff.md` :195–203); C1 S0–S3 2026-09-17→19 (~3 sessions
+ 4 audit rounds); `unseq` stages B–E5 2026-09-16→22 (~1 session per stage + fix rounds); plan §5.1's refactor estimates (P 3–4, C3 3–4,
C4 2 + re-pin, B6 2–3). «Session» = one lane-day incl. gate + audit.

| Item | What it changes in the semantics | CUSTOMER value | FIDELITY value | Cost | Deps | [AGENT] recommendation |
|---|---|---|---|---|---|---|
| E6 — trigger refinement («… or another FAILING occurrence») | lowering only (which sweeps enter the graph) | L — no core shape change | M — 21 panic-vs-panic rows keep two members (E5 handoff §3) | ½ | — | do now (dispatched) |
| E6 — non-main-unit grammar + twin re-pin | lowering; more `unseq` nodes reach the machine | L — more nondeterministic steps the customer must handle; only pays if their subject imports source units (raft twin does) | H — one model, corpus + twin | 1–1½ | — | do now (dispatched; [USER] 2026-09-22 item 2) |
| E6 — legacy triple retirement (`Stmt.unseqProbe`/`Cont.probeK`/`ChoiceSite.unseqPanic`) | −1 `Stmt`, −1 `Cont` frame, −1 choice site, −N rules | **M** — every deleted frame is one fewer lifting case and one fewer `fill` obligation | M — one mechanism, not two | ½ (after census zero) | the two above | do now — the customer-relevant half of E6 |
| Two decoder follow-ups (source-local annotation cross-check; named refusal for `after` on a literal `allocate`) | decoder (trusted surface #1) fails closed on forged wires | L — the customer inherits the wire's trust assumption (`CLAUDE.md` (1)); tighter is better, but no theorem depends on it | M | ½–1 | E6 lane | ride E6 |
| Status-diverse manifest row (apparatus, trusted surface #2) | `expected_status` as a set | L | M — one latitude class has no row today | ½ | — | later; ride the next apparatus lane |
| NaN [a]+[b] (BUG-094; [USER] 2026-09-19) | a new `ChoiceSite.nanBits`; eleven `FloatBits` arms take a rule argument | **L, slightly negative** — floats appear in no proof fragment ever attempted (park corpus, spike); one more site to quantify over | M–H — 7 red-by-design rows, a wrong-answer risk closed | 1–2 | — | DEFER behind §D items 2–4 (reorders a [USER] ruling → PENDING [USER]) |
| P — native method promotion | frontend emits no wrappers; core resolves via `FieldDef.embedded`; `Func.wrapper`, `recoverThroughWrappers`' wrapper arm, the `nilValueMethodText` family test go | **M–H** — deletes the wrapper case from row A-3's recover side condition; method-call rules become one shape | M — hop-path race footprint falls out of the C1 trace; twin re-pin | 3–4 | C1 (done) | do, after the spike says whether wrappers block `fill` |
| C3 — `Cont := List Frame` via `@[match_pattern]` views | definitional; `fill K c := ⟨mode, k ++ K⟩` becomes expressible; `EctxItemLanguage`'s `Ectx := List EctxItem` matches literally (iris `EctxiLanguage.lean`) | **H** — THE prerequisite for any bind law that is not hand-proved per program (park `Laws/Bind.lean` = the cost of not having it) | L — zero behaviour change | 3–4 | B3, B4 (done); P optional | PROMOTE to first core item after E6 (PENDING [USER]: reorders 2026-09-22's «NaN then P → C3») |
| C4 — block-scoped allocation; delete `Stmt.initialization` | fixed env per `.seq` frame; `seqCont` splice unconditional; −1 `Stmt` | M — fixed environments make `fill` and local-store laws frame-local; the park's `Laws/Init` paid for the splice | L (preserving up to heap iso; re-pin) | 2 + re-pin | B6 | keep, after C3 |
| B6 — numeric locals (`VarId := Nat`) | environments `Nat`-keyed; `$`-temporaries gone | M — the park's `Frame/Rename*`/`RenameId` (12 importers) was renaming machinery the customer had to build | L | 2–3 (twin re-pin) | — (parallel-lane-able) | keep, pair with C4 |
| End-to-end labelled simulation (OWED, `CLAUDE.md` (2)) | a stated `ProgramRun ↔ Steps/StepM` contract (init, labels, choices, memory effects, output, terminal priority, readout, refusal hypotheses — review §7) + the stream-composition theorem | **H** — this IS adequacy's bridge to `golean run` (plan §1.14(4)); without it a downstream `adequate` result is about the relation only | L — the executable is what the differential checks | 3–5 (statement note 1; seq composition 1–2; pool 2) **[inf]** | none hard; cheaper after C3 | do now-ish: the design NOTE first, then the sequential half |
| Typed-profile / admission-domain invariants (PARKED) | `Accepted P → refusal-free` for named profiles | M — only if the customer wants `adequate .NotStuck` without carrying its own hypothesis; the spike carried its own | L | H (8.4k lines parked; profile-per-fragment) | — | STAY PARKED; state the domain hypothesis FORM in the simulation note instead |
| Consumer interface facade + pin protocol (DROPPED 2026-09-11) | a re-export module + a kernel-level deletion test; a `PINNED @ <sha>` line | **H** — L9/L10/L15; two proxies died of drift already (§0) | L | 1–2 | after C3 (so the pinned `Cont` is the final shape) | REVIVE in MINIMAL form (PENDING [USER]: reverses the set-aside) |
| Differential corpus growth / fidelity lanes generally | envelopes widen ((b) → (a)); rows born | M — the customer WANTS every choice explicit («every relevant concrete choice needs coverage or a proved erasure argument», raft-proofs `…layered-refinement` §4.4), but each widening is a member they must discharge; value concentrates on THEIR subject's features (channels/maps/slices/structs/goroutines) | H | ongoing | — | continue; weight by the raft twin's feature use |
| Reduction to Go's access granularity (NPDRF; restate PENDING since 2026-09-11) | a true statement over the C1 trace | H for any concurrent claim with Go-level meaning; 0 for sequential proofs | L | VERY H (obstructions 4/6) | C1 (done) | RESTATE only (design note), no proof lane; PENDING [USER] |
| A `Language`-instance spike (in-repo, outside build + gate; F10 2026-09-05 permits «an iris-lean `Language` instance + toy facts») | none — it reads the core | **H** — the only way to learn what `fill`/`toVal`/`obs` the customer's `primStep` needs BEFORE C3 fixes the shape | 0 | 1–2 (park `Lang.lean` is 70 lines; `GateA1/Language.lean` existed at `32398203`) | — | DO NOW, in parallel with E6 (a reader, not a core writer) |

Discussion. The plan of record (E6 → NaN → P → C3 → C4 → B6) is ordered by fidelity and by «one core writer»; read against §A
it puts the two highest customer-value items (C3, the simulation) last and third-from-last, and the lowest (NaN) second.
Fidelity items with LOW proof value: NaN, the manifest row, most (b)→(a) widenings outside the customer's feature set. Proof
items with LOW fidelity value: C3, the simulation, the interface/pin, the spike — none moves a row, which is why the
2026-09-11 ruling set them aside and why the 2026-09-22 question re-opens them. Nothing in the table is BOTH high-fidelity and
high-proof except the legacy-triple retirement and P; both stay.

## C. What the roadmap is MISSING that the customer needs

| # | Candidate | Assessment | Does an existing item give it? | [AGENT] |
|---|---|---|---|---|
| 1 | A DRF-confluence lemma for `unseq` sweeps: if no two occurrences' `AccessTrace` labels conflict, every legal order yields the same `(c', σ')` — so a WP rule for `unseq` is proved ONCE at the canonical order **[inf]** | HIGH value, MEDIUM cost: C1 put the labels on `Step`; the mover lemmas exist (`NPDRF.lean`); `UnseqSound.lean` has the invariants (`unseq_pick_ready`, `unseq_done_permanent`, …) but design §3.5 says «NOT CLAIMED: … ANY ordering reduction» and §7(b)'s wire-scheduler theorem is soundness/completeness over traces, not confluence; the apparatus certifies confluence PER ROW (`lane=confluent`), which a proof cannot cite | no | add: a design note, then the lemma (2–3 sessions) after C3 |
| 2 | A schedule-level confluence (registry-point DRF) | = the NPDRF restatement (B row); very high cost | no | restate only |
| 3 | An `EctxLanguage`-shaped `Step`: `fill`, `fill_val`, `step_by_val`, `base_ctx_step_val` | C3 gives the TYPE, not the laws: `recoverResult` (side condition or P) and the abort-under-fill case (A-3) must be settled; the spike decides between «recover as a frame operation» (plan §1.7) and a value-like abort | C3 partially | spike first (§D-2), then C3 states the laws that hold, with their side conditions NAMED |
| 4 | Allocation-renaming quotient / deterministic allocation | alloc is deterministic and one-rule already (`Store.allocCell`); a WP's `∃ l, l ↦ v` needs no quotient; the quotient matters only for C4's «up to heap iso» and NPDRF obstruction 4 **[inf]** | yes (A2/C1) | none owed for the customer |
| 5 | The pin protocol + a kernel-level deletion boundary test (L10) | see B row «interface + pin»; the certified build already records compiled inputs (`tools/certification.py`), so «PINNED @ sha» has a provenance record to attach to | dropped 2026-09-11 | revive minimal |
| 6 | A sequential-fragment adequacy STATEMENT (`Steps` run → `∃ fuel ch, run = .ok`) | = the sequential half of the simulation; concretely the stream-composition theorem `Trace.lean`'s header names | the owed simulation | do first inside the simulation note |
| 7 | Output/picks as a trace the state interpretation can own (A-10) | at the pool yes; the sequential `Step` label is memory-only; a `Step`-level `Event := access ⊕ pick ⊕ out` label is a relation-shape change (every rule restated — B7/C1 showed this is mechanical, C1 D5 «per-arm restatement is mechanical») | no | PENDING [USER]: change the sequential label, or instantiate the customer's sequential `Language` over `StepE`/`StepEvent` **[inf]** |
| 8 | Panics/`recover` frame discipline as laws | B4 regularized the shape; the laws (`wp_call` with defers, unwind) are the customer's; what we owe is A-3's side condition stated once | C3 + P | covered by §D-2/3 |
| 9 | The pool's shape for a concurrent logic (per-thread WP, fork rule) | `StepE` is fork-rule-shaped; pairing needs the customer's LangD-style decomposition or OUR per-thread restatement of `StepM`; B4's `Park` type OWED | no | defer until the customer's first concurrent subject; record as owed |

Discussion. Items 1, 3, 6 are cheap relative to their value and are absent from every plan since 2026-09-11 because the
ruling removed the customer axis; item 7 is a shape decision that gets more expensive after C3 and the pin, so it belongs
in the spike's questions. Items 2 and 9 are the concurrent frontier — real, expensive, and not what a first downstream proof
consumes.

## D. A proposed re-prioritized sequence (all [AGENT]; each reorder PENDING [USER])

1. **E6 as dispatched** (trigger, non-main grammar + twin re-pin, legacy triple retirement; the two decoder items ride) — ~2 sessions, the one core writer.
2. **In parallel, a reader lane: the `Language`-instance spike** over main's `Step` (5-ary), outside build/gate/ci graph (F10 2026-09-05 shape): must answer (i) does `fill := k ++ K` satisfy `Context` modulo `recover`; (ii) abort under `fill`; (iii) what goes in `obs` (C-7); (iv) `toVal`. Exit = a 2-page findings note, no code kept. ~1–2 sessions. PENDING [USER] (within the 2026-09-11 «limited spikes» latitude).
3. **The labelled-simulation DESIGN NOTE** (statement only: init, labels, choices, memory, output, terminal priority, readout, refusal hypotheses; the sequential stream-composition theorem as its first deliverable) — 1 session; the sequential proof 1–2 sessions; the pool half after C3.
4. **C3** with the context laws that hold STATED (side conditions named per the spike) — 3–4 sessions. G-C3 was ruled in principle 2026-09-04; re-confirm under the customer framing. PENDING [USER].
5. **The `unseq` DRF-confluence lemma** (design note, then proof) — 2–3 sessions. New item.
6. **P → B6 ‖ C4** as planned (P first if the spike shows wrappers block `fill`; else B6/C4 first).
7. **Minimal interface + pin record** (re-export module, deletion test, `PINNED @ sha` with the certified-build inputs) — 1–2 sessions. PENDING [USER]: reverses the 2026-09-11 set-aside of «customer pin / release protocol».
8. **NaN [a]+[b]** — after 3 (or as the NEXT core lane after E6 if the [USER] keeps the 2026-09-19 order; it is small and independent). PENDING [USER].
DROPPED/DEFERRED vs today's plan: NaN moves from 2nd to ~8th; NPDRF stays restate-only; typed profiles stay parked; fidelity lanes continue but weighted by the customer subject's features; the pool-side simulation and the concurrent shape (C-9) wait for the customer's first concurrent subject.

**PENDING [USER] questions, in priority order.**
1. **Where is the logic?** No checkout under `deps/`; `deps/reasoning-revival/raft-proofs` is a Lean-only Verdi/etcd mirror repo (origin `OathTech/raft-proofs`) that imports nothing from GoLean and itself names the logic as an external, not-yet-built dependency. Which GoLean SHA does the logic build against today, is it sequential-first, and which language features does its first subject use? (Everything above sharpens once this is known.)
2. Approve the reorder: C3 + the simulation note + the spike ahead of NaN and P (§D-1…5 vs the 2026-09-22 «then NaN, then P → C3 → C4 → B6»).
3. Authorize the `Language` spike as a reader lane (F10 shape; no build/gate footprint).
4. Revive a minimal interface + pin record (reverses part of the 2026-09-11 set-aside; §B row, §C-5).
5. The sequential `Step` label: memory-only (today) vs `Event` (access ⊕ pick ⊕ out) — a relation-shape choice best made before C3 and the pin (§C-7).
6. Confirm NPDRF stays restate-only (design note, no proof lane) under the customer framing.
7. NaN lane timing (§D-8).
