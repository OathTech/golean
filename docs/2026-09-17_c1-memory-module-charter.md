# C1 work charter — the memory module and the access trace, under the 2026-09-11 ruling

[AGENT] planning worker, lane `plan/c1-memory-module-0917`, 2026-09-17, at main `7050bb9c`; records only, no lake/lean run. The brief for the C1
implementation lane and a DESIGN GATE: the [USER] reads §7 before dispatch. Every code anchor is `file:line` at `7050bb9c`, read for this note. C1 is
the second rung of the state-cleanup ladder (B7 → C1 → P → C3 → C4 → B6, `docs/2026-09-03_design-hygiene-arc.md`); B7 landed its seam (`Store {heap :
Heap}`, `GoLean/GoCore/Store.lean:25-27`; `docs/2026-09-17_b7-context-store-handoff.md` §9). Sprint-era inputs
(`docs/2026-09-04_reasoning-surface-plan.md` §1.2/§1.14/§6 L7, `docs/2026-09-06_c1-contract-handoff.md`) are reused for their DESIGN content only;
every justification that named a downstream logic is re-justified below by the semantics' own quality, or dropped (§9).

## 1. Authority and objective

Authority ([USER] Mike, 2026-09-11, verbatim, relayed by the [AGENT] coordinator — cite as relayed): «okay, I am still concerned that we are not
focusing our energy on actually making the *go semantics* as good as possible. We don't have as of now a customer. Our job is to make the Go seantics
as good as we can make it. Nothing else. We can do limited spikes to try to validate our choices, but our top level goal is to make the semantics
good. We should prioritize high value efforts, like cleaning up the handling of state, and making the semantics structure regular. We *can* provide a
relational definition along with it too. Everything else should be dropped». Recorded in `docs/2026-09-11_review-dispositions.md` §4 step 3. The
boundary is CLAUDE.md's «What this repo provides, and does not» ([USER] 2026-09-16): a Go semantics via GoCore, a relational semantics provably
equivalent to it, NO higher-level reasoning. Nothing in C1 is a points-to, a ghost heap or an ownership law; §5's law is a law OF THE MEMORY MODULE
(disjoint writes that do not commute are a defect of the model), not a downstream ask.

**Objective, in the semantics' own terms.** Memory is handled today in three places that must agree and are not proved to: the operations
(`loadLoc`/`storeLoc`, `Ops.lean:1342/1374`; the payload readers/writers, `Store.lean:62-102`); the detector's FOOTPRINT TABLE beside them
(`stepAccesses` over 17 `Config` shapes, `Race.lean:1582-1663`; `strictOpAccesses` :509, `stmtOpAccesses` :701, `storeTargetAccess` :1521,
`dispatchAccesses` :647, `deferEntryAccesses` :692, `projChainTarget` :577, `unseqRunAccesses` :1537 — 54 mention lines in `Race.lean`, 6 in
`Multi.lean`, 5 in `NPDRF.lean`); and a 256-line prose inventory (`Race.lean:1-256`) whose agreement with the operations is, in its own words, «a
LOCKSTEP obligation … a theorem nobody has». C1 makes ONE module own the representation, the operations AND the access events: every operation EMITS
what it touched, by definition, and a step's footprint IS the trace its operations emitted — «footprint by definition». One source of truth: a new
`stepFn` arm cannot forget its footprint (there is no second account); the detector (`raceUpdate`, `Multi.lean:1845`) and the fine-race proposition
(`RacyFine`, `NPDRF.lean:427`) CONSUME the trace instead of recomputing a table from configuration shapes; the inventory shrinks to the list of loads
that are deliberately NOT accesses (§3). The same module fixes, by construction, both measured costs of `docs/2026-09-11_bug090-rediagnosis.md` §3,
re-anchored: **A** — a path write re-normalizes its whole root (`storeLoc` `Ops.lean:1374-1392` recurses to the root arm :1376-1379 via
`StructFields.set` `State.lean:153-166`/`arraySet` `Ops.lean:323-330`; `normalizeListWith` `#[head] ++ tail` :1107-1112; in-place `append` one such
write per element, `Machine.lean:1360-1369`); **B** — the pre-step store stays referenced across the step, so every cell write copies the heap
(`raceUpdate ctx m.shared m.threads ev m' r` AFTER `stepMulti ctx m`, `Multi.lean:2198-2199/2208-2209/2249-2250/2264-2265`, signature `(sPre : Store)
(tsPre : Array Thread)` :1845; `deliverS` returns the PRE-apply store on its panic arm, `StepFn.lean:58-64`, so every apply arm holds `s` across the
apply, e.g. :536/:544). C1 claims NO fidelity progress: zero rows move, or the slice stops (§6).

## 2. The representation question — options, costs, recommendation

**(i) Keep the dense `Array HeapCell` (`State.lean:68`; address = index, A2) and fix A and B in place.** Fix A: a leaf write descends the ROOT's
declared `Ty` along the path (`.field tid f` → the struct def's field type via `ctx.types`; `.index` → the element type), normalizes the INCOMING leaf
at that type and updates the leaf in place — `Array.modify` discipline on the heap slot and on each array along the path (the cell taken OUT of the
heap while rebuilt, else inner arrays copy at RC 2 — the benchmark verifies). Whole-value normalization stays for root stores only, made LINEAR
(`push`/`mapM`, never `++`). Sound only under a NORMAL-FORM INVARIANT the machine does not state today — `StateWf σ := Store.locSup σ ≤ σ.nextAddr`
(`StateWf.lean:672`) is a bound, not heap typing (review §6): `HeapNormal ctx s` := every value cell satisfies `isNormalForTy ctx.types ty v`
(`Ops.lean:1322`), with the congruence «a normal root updated at one leaf by a value normal at the leaf's type is normal». Without that fact, skipping
the root re-normalization is a wrong answer waiting for a non-normal cell (the sprint handoff's byte-store counterexample). Establishing it closes the
alloc hole — `Store.alloc` does not normalize (`Store.lean:38-42`; 9 `s.alloc` sites in `Machine.lean`, e.g. `.allocNew` :1087, `bindParams`
:663/:673) — a BEHAVIOUR-change candidate (a never-stored cell may hold a non-normal value today); the differential decides: zero drift, or a BUG with
a red-first row, referred (arc invariant 1). Fix B: (a) `raceUpdate` loses `sPre`/`tsPre` — the `StepEvent` (`Multi.lean:936`) carries the trace (§3)
and the pre-state facts its HB arms read today (`chanCell sPre loc`, the sync pre-cell, the pre-config shapes matched at :1818/:1722/:1773/:1682); (b)
`deliverS` becomes validate-then-commit — per apply arm the theorem «`.panic` ⇒ store unchanged» (pattern: `storeLoc_base_noPanic`
`MachineSound.lean:3725`), so the panic arm returns the store it was GIVEN; an arm that writes then panics (S0 audits every arm) gets a per-cell undo
entry inside the module, never a whole-state copy; (c) the enumerator (`EnumDedup`) pays an explicit copy at each fork, not per write. Cost:
`HeapNormal` threads through `step_preserves_wf` (`StateWf.lean:6811`) and the helper-preservation family; one leaf-descent lemma per `Ty` shape; a
driver-side rewrite. Every `heap[i]` proof (`Heap.lookup` `State.lean:128-130`, `storeLoc_root_frame` `NPDRF.lean:475`) is UNCHANGED.

**(ii) A persistent map keyed by `Addr` (`Value.lean:482`).** O(log n) writes with no copy-on-write hazard even under retention, but every `heap[i]`
proof re-states; `Heap.locSup`'s fold (`StateWf.lean:153`), `Store.eqb` and the dedup node hash need a canonical form; «every address below the size
has a cell» stops being true BY TYPE and returns to the call-graph invariant BUG-085 had to audit (`docs/BUGS.md:5049`); and it does not touch cost A
— B is a RETENTION defect, not a representation defect. REJECTED [AGENT]; §7 D2.

**(iii) Granularity: root cells vs leaf cells.** A cell is a whole Go value at a declared type; a `Loc` (`Value.lean:674-677`) is `base | field |
index` — a PATH into it; the conflict relation is path-prefix overlap (`locOverlap` `Race.lean:314`; `ShadowKey.overlap` :360-367, with
`syncWord`/`chanObj` keys beside `data`). Leaf cells (heap keyed by leaf paths) make every composite load a materialization (Go copies structs
constantly), change what `PoolResult.done`'s whole-`Store` comparison and `storeLoc_root_frame` say, and move BUG-041's semantics — while the detector
already HAS leaf granularity in its conflict relation, independently of cell granularity. **Recommendation [AGENT]: root cells with path-addressed
leaf OPERATIONS of cost O(depth) — option (i)**; the relation's footprint shape is unchanged (`RaceAccess := AccessKind × Loc`, `Race.lean:470`, is
the `.data` case of §3's atom). Alternative, named: leaf cells — only if the [USER] wants per-leaf identity as the MACHINE's notion of a location;
cost VH, own charter. §7 D1.

## 3. The access trace

**Atom and vocabulary.** `Access := AccessKind × ShadowKey` — `AccessKind ∈ {read, write, atomicRead, atomicWrite}` (`Race.lean:391-395`, mem#model's
two axes) × `ShadowKey ∈ {data l, syncWord l kind word, chanObj l}` (:342-352); `RaceState.accessKeys` (:997-1000) already folds this type.
`AccessTrace := List Access` (not `Trace`: `GoLean/GoCore/Trace.lean:15` is the n-step run relation). No `alloc` event (Go has no `free`; a fresh cell
is visible in the store, not the trace — the inventory's malloc convention); no `range` atom (multi-element operations emit one `.data` atom per
element via `sliceElemLocs` :473, so `ShadowKey.overlap` stays the ONE conflict table). NOT an access — hence a `peek`-class operation whose every
call site is enumerated in the module's docstring with its gc argument (review §9's warning; today's rows `Race.lean:180-232`): address formation
(`indexTargetLoc` loads the base to bounds-check, `Machine.lean:243`; `resolveChain` :1633-1640 through it), metadata inspection (`len`/`cap`, array
sizes), the module's own path descent, fresh allocation, driver readouts, pool bookkeeping. Payload and sync traffic is SYNCHRONIZATION, never
`.data`: channel operations emit `chanObj` accesses at gc's instrumentation points (send entry, close success, select's send-clause poll — U3, today
`raceChanEntryReads`); the sync primitives' state transitions (`.syncData` stores, `Machine.lean:3586-3727/:3885`) emit `syncWord` accesses
(`syncEntryKinds` :1428 / `syncReleaseTailKinds` :1496 — U4); atomics emit `atomicOpKind op` (:1208) at the cell's `.data` path.

**Where emitted — inside the module, by definition, never by the caller.** Operations: `alloc` (emits nothing; normalizes), `load l` (`[(read, data
l)]`), `store l v` (`[(write, data l)]`, leaf-normalized), `peek l` (nothing), `loadFor root leaf` (loads the ROOT value, emits the read at `leaf` —
`projChainTarget` :577-585 becomes this operation's definition: gc compiles `p.a`/`a[1]` to one leaf load, mem#restrictions' per-sub-value license
quoted at latitude C10; the CALLER — `evalVar`/`deref` with the continuation in hand — chooses the leaf, a semantic statement about what Go reads
here, not an emission), `atomic op l`, `syncStep l pre post` (the word accesses), the four payload operations (`chanObj` where gc instruments). A
caller chooses an OPERATION; it never constructs an `Access`. `stepFn` (`StepFn.lean:255`) returns the trace as a fourth component; `Step`
(`Machine.lean:4390`) carries it as a LABEL (the «memory effects» component of the labelled simulation CLAUDE.md (2) owes); `StepM`'s
(`Multi.lean:2423`) `thread` rule lifts it into `StepEvent` (alternative: §7 D5).

**How the detector consumes it.** `raceUpdate` = a fold of `ev.trace` through `RaceState.accessKeys` plus the HB arms driven by `ev.action` and the
carried pre-state facts (§2 B(a)); `footprintsConflict` (`NPDRF.lean:416-417`) and `RacyFine` (:427-436) restated over the two goroutines' next-step
labels with `ShadowKey.overlap` and `AccessKind.conflicts` (:410); the table family DELETED (tombstoned), `Race.lean:1-256` replaced by the module's
`peek`-list docstring. The DATA footprint does not depend on the stream (Stage B's rule, `2026-09-16_unseq-stage-b-handoff.md` §2 «phases»); sync-word
emissions MAY (`tryLock`'s pick decides `acquired`) — hence a label of the step taken, not a function of the pre-configuration.

**The trace-equality audit — THE regression for the retirement.** Over the whole corpus (3,676 rows at B7's gate; every stream a row enumerates) and
the raft twin (`scripts/check-frontend-pins`' pinned wire), the module's emitted `.data` trace per step must EQUAL today's `stepAccesses ctx s c` as a
MULTISET (order within a step is not pinned — the fold is a set), and the `syncWord`/`chanObj` emissions must equal what `raceUpdate`'s arms recorded;
a tracer mode beside `scripts/choice-trace-corpus`, BOTH accounts in the SAME binary while the table still exists, differences dumped per (row,
stream, step). EVERY difference is a FINDING — a BUG entry, a red-first corpus row, a [USER] referral — never absorbed as «preservation», never
filtered to match. The universal companion (§7 D6): `accesses_eq_stepAccesses` per `stepFn` arm, up to permutation, proved at the commit that deletes
the table (the G-C1 text, [USER] 2026-09-04; the theorem leaves with the table it audits, its proving SHA recorded). **BUG-041** (`docs/BUGS.md:981`;
the O1 residual `race/free/array-dyn-index-read-write`, pinned FAIL): the dynamic-index read `a[i]` is whole-cell on BOTH sides (the index is
unevaluated when the base is read), so the audit expects EQUALITY there, the row stays FAIL, and the over-report is INHERITED by the trace, rowed
under BUG-041; a narrowing the construction happens to produce is a PASS flip = a detector-semantics change → BUGS.md `Cases:` line, disclosed,
referred (§7 D7). The wrapper-hop narrowing at frame entry (`dispatchAccesses` :647 via `wrapperForwardArg` :616) stays the dispatch operation's
emission until P removes the wrappers.

## 4. What the module must keep expressible

- **Stage B's binder cells and frozen target identity** (`2026-09-16_unseq-stage-b-handoff.md` §2 «cell scope», «target operands»): binder cells are
  ORDINARY store cells declared into the source scope (`allocDecls`) — no new cell kind; a `TargetRef` whose anchor is a frozen header VALUE resolves
  through `resolveChain` at store time without re-reading the variable (R4) — writes are addressed by a root VALUE plus a path (`storeTarget`
  `Machine.lean:1646-1650`); `unseqRunAccesses`'s emissions become the run step's operations'.
- **Map and channel payload cells** (`HeapCell` `State.lean:30-59`): whole-payload replacement (`Store.lean:81-102`) with the B1 identity stamps —
  `nextId` monotone and never reused is an invariant OF THE CALLERS (`mapAssignValue`) the module's map write must keep provable (state and prove it,
  or refuse a decreasing counter by name — the lane's choice, disclosed); FIFO/capacity/closed for channels; chan/sync loads remain synchronization
  (§3); refusal texts byte-preserved.
- **`HeapNormal`** (§2 (i)): what it is FOR — int kind-width masking, float bit canonicalization, the nil-channel canonical form, struct tag/field
  alignment (`normalizeValueForTyTy` `Ops.lean:1165-1205`) are LEAF facts, and the disjoint-path law (§5) needs typed storage to be true of leaf
  writes (review §6); where MAINTAINED — at `alloc` and at every `store` (per leaf), stated once as a `StateWf` conjunct and preserved by
  `step_preserves_wf`, never re-computed per write. `isNormalForTy_sound` (`StateWf.lean:1572`) is the direction already proved.
- **`Store.updateCell`'s refusal texts** (`Store.lean:49-55`): the `.internal` «allocation goes through `ExecState.alloc` only» (:55) is C1's to
  refresh (RULED [USER] 2026-09-17, B7 handoff §8 item 3) → «… (allocation goes through `Store.alloc` only)»: [AGENT] intends; an `.internal` on a
  path no well-formed run reaches (A2), not differential-visible; object at §7 D10. Every `stuck`/`panic` text of `loadLoc`/`storeLoc`
  (`Ops.lean:1346-1400`) and the payload readers is byte-preserved; a refusal the leaf descent introduces reuses the existing text for an existing
  condition, else is NEW, named, unreachable.

## 5. The validating spike (allowed, small, disposable; never a deliverable)

Question: **does the candidate representation admit a disjoint-path frame law, including the SAME-ROOT half `NPDRF.lean:119-130` (obstruction 6)
records as unproved?** Lemma shapes on the module's interface, for `ShadowKey.overlap (.data l) (.data m) = false`: (F1) `store l v; load m ≈ load m`
— same value, and the store differs from the pre-store only at `l`; (F2) `store l v; store m w ≈ store m w; store l v` — equal stores, traces
permuted. A ≤1-session Lean spike checks BEFORE S1 is committed, against `Store` + a stub module with the leaf-typed write: (a) `StructFields.set` at
distinct field names and `arraySet` at distinct indices commute (the two lemmas obstruction 6 names); (b) the leaf congruence «normal root + normal
leaf at the leaf type ⇒ normal root after the write» at one `.field` and one `.index` depth; (c) F1/F2 STATE and typecheck against the stub, F1 proved
for depth ≤ 2. PASS = (a)–(c); anything else = STOP and re-plan (§6's estimate is void; §7 D2 is re-posed with the obstruction). It lives under
`spikes/c1-frame/`, outside the lakefile and the gate (CLAUDE.md's spike clause), lands only as EVIDENCE (SHA, build line, the proved statements) and
is deleted or left dark (B7's D7 shape) at landing.

## 6. Slices and gates

Each slice is ONE gated runtime commit: `scripts/capped scripts/ci --diff` at ZERO baseline drift (the expected 5a-class `certificate provenance`
STALE line named as such, as at B7), the whole-corpus choice trace byte-identical (`scripts/choice-trace-corpus --dump`, `cmp` of sorted dumps), no
wire change, no `sorry`/`axiom`/`native_decide`, no `partial` in `GoLean/GoCore/`, lemmas restated arm-for-arm, deletions tombstoned. A
`State.lean`/`Store.lean` edit is INTERFACE-HOT (B7 measured the `GoLean.GoCore` warm after a `State.lean` touch at 104 s; re-measure at S0). **One
core writer**: the lane owns `GoLean/GoCore/**`, `GoLean/CLI.lean`, `GoLean/ChoiceTrace.lean`, `GoLean/EnumDedup.lean`, `Tests/**`;
frontend/decoder/corpus lanes stay in `GoLean/NativeToIR.lean`, `tools/nativefrontend/**`, `Corpus/**`.

| slice | content | done when |
|---|---|---|
| S0 records (+ the §5 spike) | census at the fork by recorded grep (this tip: `loadLoc ctx`/`storeLoc ctx` call lines Machine 18/29, StepFn 1/1, Multi 2/4, Race 2/0, Ops 4/0; payload ops Machine 4+11+3+5, Multi 25+5, Race 1+1, Ops 1; the table family 54/6/5); the apply-arm write-then-panic audit (§2 B(b)); the benchmark BEFORE — `docs/evidence/2026-09-11_bug090-rediagnosis/run-probes.py --plan full` (3 runs, medians, net of the empty probe) with the fork's certified binary; the warm measurement | recorded; spike PASS |
| S1 the module + cost A | `GoLean/GoCore/Mem.lean` (or `Store.lean` grown): leaf-typed `store` with the `Array.modify` discipline, linear normalizers, `alloc` normalizes; `HeapNormal` + the congruence lemmas; `loadLoc`/`storeLoc` KEEP their names as the module's `load`/`store` (StateWf mentions 17/45, MachineSound 13/12 — renaming buys nothing); `StateWf` gains the conjunct; `step_preserves_wf` re-proved. No trace yet | gate green at zero drift; **write_fixed flat**: per-write net within 2× across m = 10…10,000 (today 15 µs → 109 ms); **append_grow n = 4,000 net < 2 s** (today 31.6 s), successive ×2 ratios ≤ 2.2; per-step baseline (`scalar` 80k) within 10 % of BEFORE |
| S2 the trace + the fold (cost B(a)) | `AccessTrace`; the operations emit; `stepFn` 4th component; `Step` labelled (D5); `StepEvent.trace` + the carried pre-state facts; `raceUpdate` without `sPre`/`tsPre`; `RacyFine`/`footprintsConflict` restated; the trace-equality audit with BOTH accounts live, differences rowed; then `accesses_eq_stepAccesses` (D6), the table family + `Race.lean:1-256` deleted, the `peek` list written | gate green; audit: 0 unrowed differences; `scripts/detector-soundness --select in-scope` re-run — HOLE = 0, other cells unchanged (`docs/2026-09-02_detector-soundness.md` §2); coherence theorems re-proved with the label |
| S3 the rollback (cost B(b)/(c)) | `deliverS` validate-then-commit with the per-arm «panic ⇒ store unchanged» theorems (undo entries only where an arm writes then panics); the enumerator's explicit fork copy | gate green; **alloc_new linear**: n = 1k/4k/16k/32k successive ×4 ratios ≤ 4.4, n = 32k net < 1 s (today 14.05 s); **the (h) scalar phase flat**: 20k iterations after 40k live cells within 1.2× of 0 live cells (today 7.35 vs 0.246 s); the whole BEFORE plan re-run, 3 runs |

Targets are [AGENT] proposals, measured as the BUG-090 note measured (same probes/runner/box class, load noted, median of 3, net of the empty probe);
a miss is reported as a miss, never re-fitted. Maps (`mapEntryIndex?` `Ops.lean:2148-2157`, ≈11 ns per live entry per write) are NOT a C1 target
(bug090 §5 item 5; a later slice). **Session estimate, CONDITIONAL on (i) + the spike passing + S0's warm ≤ 5 min:** S1 1–2 sessions (the `HeapNormal`
threading through the ~7k-line `StateWf.lean` is the unknown), S2 2–3 (the label on `Step`/`StepM` and the restatements are B7-class mechanical churn;
the audit and its differences are the real work), S3 1 — **4–6 sessions**; −1 if D5 defers the relation label; +2 and cost A untouched if (ii) is
chosen. **Left to C3**: the frame list (`loadFor`'s caller reads the continuation's projection chain; C3's `Cont` reshape touches the caller, not the
module). **Left to C4**: block-scoped allocation/reclamation (C1 adds no `free` operation or event; C4 adds them under its own heap-iso gate if it
reclaims). **Left to P**: the wrapper-hop narrowing (§3).

## 7. Decisions for the [USER] — posed, not ruled; [AGENT] recommendations marked

**Provenance, corrected at the C1 audit fix round (2026-09-18, [AGENT]; audit F1 — the earlier header here read «RULED
[USER] 2026-09-18 … by default acceptance», which the cited record does not support: `docs/2026-08-31_qrow-rulings.md`'s
«The on-deck decisions ruling record (2026-09-18)» contains rulings (1)–(4) and no [USER] text on D1–D7, D9, D10).**
D1–D7, D9, D10: the [AGENT] recommendations below were taken as the lane's brief on the **[AGENT] coordinator's reading of
the [USER]'s 2026-09-18 non-objection to the triage** that classed them as doctrine-determined or gate-arbitrated defaults —
NOT a [USER] ruling; **explicit [USER] ratification is REQUESTED at the merge ask (PENDING [USER])**, one line each or one for
all, to be recorded verbatim in the qrow record and cited here. **D8** IS ruled — ruling (4), [USER] Mike 2026-09-18, verbatim,
relayed: `NPDRFReduction` is DEPRECATED / marked unsound, NOT deleted, and restated after C1's trace exists — C1's S0 carries
the marker as a records-class core edit. **Sequencing after C1** (ruling (1), [USER]): Stage C of the evaluation-order plan,
then P → C3 → C4 → B6.

- **D1 Cell granularity.** (a) root cells + path-addressed leaf operations (§2 (iii)); (b) leaf cells. **[AGENT] recommends (a)**: the conflict
  relation is already leaf-granular; (b) changes the relation's footprint shape and every root-cell theorem for no fidelity gain.
- **D2 Representation.** (i) dense array, A and B fixed in place; (ii) persistent `Addr` map. **[AGENT] recommends (i)**; (ii) does not touch A and
  surrenders density-by-type.
- **D3 `HeapNormal` as a `StateWf` conjunct + `alloc` normalizes.** A RESTATEMENT of `StateWf`/`MachineWf` (none weakened) and a candidate behaviour
  change at never-stored cells. **[AGENT] recommends both**; the differential arbitrates the second — any drift is a BUG, red-first, referred, never
  absorbed.
- **D4 «Preserve only up to heap iso» (allowed for C3–C5 by the arc).** **[AGENT] recommends NOT claiming it for C1**: zero drift on the machine and
  the byte-identical choice trace stay the regression; nothing in §2–§3 needs it (addresses, allocation order, cell contents unchanged by
  construction); needing it is a STOP, not a claim.
- **D5 The trace's home in the relation.** (a) `Step`/`StepM` labelled now; (b) executable trace only, `RacyFine` over `stepFn`'s trace (an
  executable-dependent proposition, marked), label deferred to the labelled-simulation obligation. **[AGENT] recommends (a)**: the label IS the
  «memory effects» component CLAUDE.md (2) owes, and B7 showed the per-arm restatement is mechanical.
- **D6 The audit's form.** (a) the per-arm theorem `accesses_eq_stepAccesses` (the G-C1 text); (b) the executable whole-corpus + twin audit; (c) both.
  **[AGENT] recommends (c)**: (a) covers configurations the corpus never reaches, (b) is the gate-time evidence; the theorem leaves with the table,
  its SHA recorded.
- **D7 Known differences at landing.** BUG-041 rows: EQUAL expected, pin stays FAIL; a narrowing = a `Cases:` flip, disclosed, referred. Any OTHER
  difference = STOP, BUG, red-first row, referral. **[AGENT] recommends exactly this**; no class of difference is pre-approved.
- **D8 The `NPDRFReduction` interplay** (restate-vs-delete PENDING [USER], dispositions §3 item 2). C1 restates its INPUTS (`RacyFine`,
  `footprintsConflict`) over the trace and re-types `NPDRFReduction` (`NPDRF.lean:447-449`) without touching its statement beyond obstruction 5/6's
  wording. **[AGENT] recommends PROCEED with the trace as the contract** — neither waits on the other.
- **D9 Sync-word and chan-object emissions IN the module** (§3) vs a `.data`-only trace with `raceUpdate`'s arms kept. **[AGENT] recommends
  in-module**: otherwise two accounts remain (the fold's arms and the operations), which is the defect C1 removes.
- **D10 `Store.updateCell`'s wording** (§4): «… (allocation goes through `Store.alloc` only)». [AGENT] intends; object here.

## 8. Exit evidence

Gate lines (command, captured `EXIT=`, wall, SHA/tree) for the needed warms and the three `ci --diff` runs; the three sorted choice-trace `cmp`
results; the trace-equality audit's summary (rows × streams × steps compared; differences by class, each with its BUG/row); the detector-soundness
matrix before/after; the benchmark BEFORE/AFTER tables with the targets beside them — in a SMALL evidence dir
`docs/evidence/2026-09-XX_c1-memory-module/` per `docs/evidence/README.md` and `scripts/check-evidence-size` (bulk to an archive branch + manifest).
By recorded grep: the table family 54/6/5 → 0; `Race.lean:1-256` → the module's `peek` list; `raceUpdate`'s `sPre`/`tsPre` gone; `deliverS`'s
saved-store arm gone. Records in the landing commit (arc invariant 6): the «Landing record» row in `docs/2026-09-03_design-hygiene-arc.md`; slice
entries in `docs/hygiene-slice-log.md`; `LANDED <sha>` on the master plan's C1 row (`docs/2026-09-05_master-plan.md:499`); BUG-090 re-measured (corpus
consequences revisited per bug090 §5); BUG-041, `NPDRF.lean` obstructions 5/6 and latitude C10 re-anchored; D1–D10 in
`docs/2026-08-31_qrow-rulings.md`. The handoff `docs/2026-09-XX_c1-memory-module-handoff.md`: commits, gate lines, [AGENT] choices with alternatives,
tombstones, audit findings, PENDING [USER] items. Then the pre-merge adversarial audit ask, unconditional; scope and waiver the [USER]'s. No merge, no
push.

## 9. What this charter does not do

No P, C3, C4, B6; no map index; no wire change; no baseline re-pin; no BUG fix (a found wrong answer goes red-first, referred); no `free`. No
customer, adapter, interface, points-to, ghost heap, fractional or split ownership law, `Store.toKeyMap`, `stateInterp` or adequacy statement — the
sprint handoff's «Invariants the customers actually consume» section is DROPPED whole (`heapToMap`, fractional reads, Iris fixtures, the facade
inventory); harvested from it, as semantics-owned: the entrypoint table, the id-monotonicity finding (§4), the byte-store counterexample (§2), «the
detector fold owes more than `stepAccesses`» (§3's sync/chan emissions), «HOLE = 0 is weaker than the detector gate» (§6 S2 keeps both), «filtering a
trace to match the old table is not an argument» (§3). From the reasoning-surface plan: the `MemM`/`peek`/frame-lemma design and L7's granularity
remark are reused; §1.14's ghost-state/adequacy content is not. The §5 spike validates a choice of OURS and lands nowhere but the evidence dir.
