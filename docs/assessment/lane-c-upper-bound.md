# Lane C — upper-bound audit (C3): the machine side (2026-08-31)

Provenance: [AGENT] lane-C worker under the fidelity-assessment plan
(`docs/2026-08-31_fidelity-assessment-plan.md`), fidelity-assessment
branch. Claim audited: **C3 — modeled ⊆ permitted AND permitted ⊆
modeled at every latitude point.** All code citations verified at this
tip (branch `fidelity-assessment`, base `86180a5b`); doc citations
name their file. Grading vocabulary per plan Phase 0.

## Summary

The machine's nondeterminism accounting is in genuinely good shape at
the STRUCTURAL level: every choice consumption in the semantic core
flows through one tagged combinator (`Choices.consumeAt`,
`GoLean/GoCore/State.lean:263`) over an exhaustiveness-checked
9-constructor census datatype (`ChoiceSite`, State.lean:207), each
site carries an in-situ envelope statement with verbatim spec text,
and the latitude inventory's §10 counts reconcile with the code. The
`c % bound` pop (State.lean:156–160) makes junk streams impossible at
the plumbing level: no stream can select outside a site's menu, so
modeled ⊆ permitted reduces to MENU correctness per site — which is
argued (spec-quote + audit review), never mechanically checked,
because "the too-wide direction has no oracle"
(`docs/2026-08-04_nondeterminism-doctrine.md:274–276`).

**permitted ⊆ modeled fails, by the machine's own honest records, at
24 pinned/narrowed rows** (17 (b) + 7 (b-n), inventory §10) — every
one a standing debt under the new goal — and at the sub-boundary
scheduling granularity residual, whose discharging argument (the
NPDRF reduction) exists only as a DRAFT statement that is **refutable
as written** (`GoLean/GoCore/NPDRF.lean:31–35,42–48`). The two
theorem-grade ARGUED-AWAY discharges both have condition problems
after the 2026-08-31 repo split: the C11 allocation quotient's
theorem (`Frame.allocatorIndependence`) now lives ONLY on the parked
reasoning branch — this repo cites a theorem it neither contains nor
builds — and the DRF-SC argument (register #4) rests on detector
completeness that Lane A is separately asked to audit.

### Top 5 findings

1. **(F1) The C11/register-#6 quotient discharge is now an off-repo
   citation.** `Frame.allocatorIndependence` and its design note left
   with the repo split (present only at
   `park/reasoning-2026-08-31:proofs/GoLeanProofs/Frame/AllocIndep.lean`;
   `docs/2026-08-13_executable-frame-theorem.md` is gone from this
   tree, yet inventory C11 and doctrine register #6 cite both as the
   discharge). The machine here can now drift from the machine the
   theorem was proved against with nothing to catch it. REOPEN (S–M).
2. **(F2) The registry-granularity argument is a draft, not a
   theorem, and the draft is refutable.** Register #5's "sound only
   where scheduling is unobservable between [boundaries] for
   race-free programs" rests on `NPDRFReduction`, which NPDRF.lean's
   own scaffold-status block says "no theorem in the repo claims it,
   nothing may cite it … it is refutable as written (obstruction 4)".
   The largest ARGUED-AWAY row in the table is therefore an argument
   SHAPE with named obstructions, not an argument. KEEP the honest
   labeling / REOPEN the proof (L) — and until then, C3's grade at
   this row can be at most WEAK-conditional.
3. **(F3) modeled ⊆ permitted has no mechanical guard anywhere — it
   is an audit-discipline claim.** The recorded instrument is
   "envelope fidelity is a standing audit dimension … because the
   too-wide direction has no oracle" (nondeterminism doctrine
   :274–276). Menu-construction correctness (`runnableIdxs`
   Multi.lean:220, `mapIterCandidates`/`mapIterMandatoryRemains`
   StepFn.lean:605–633, `clauseReady` Machine.lean:1423,
   `appendSpillUpper` Ops.lean:1964) is spec-quoted in situ but only
   differentially tested at members gc happens to realize. For
   spec-SILENT rows (C1–C5, C8) over-width is definitionally
   impossible; the residual risk concentrates in the spec-CONSTRAINED
   envelopes (E9's production-table encoding, C6 readiness, R2's
   upper end) and in the interpretive conditions they lean on
   (I-1/L-012, I-2/L-013). KEEP with the new argument stated in §2 +
   one cheap REOPEN (S): an executable menu-invariant check.
4. **(F4) The deviation queue's guards are close to nonexistent, and
   the one planned cheap fix never shipped.** E3/E4 and E5 —
   deterministic divergences from gc, recorded since BUG-032 — have
   NO guard of any kind: no corpus case, no baseline row, BUGS.md
   records `Pinned-by: none` (docs/BUGS.md:1383); only probe
   evidence directories. E7's guard (`scripts/check-frontend-pins`
   check 1) asserts OUR realized order on ONE corpus case; the
   fail-closed hidden-dep DETECTOR that the re-envelope charter
   ruled must ship FIRST ("so the unguarded silent-divergence class
   is visible even if the full envelope slips",
   `docs/2026-08-20_w32-re-envelope-charter.md:322–325`) was in
   slice 3, and slice 3 NEVER RAN (`docs/w32-log.md:993–995`,
   graded CARRIED). E7 and E5 lose VALUES, not just panic identity.
   REOPEN: E7 detector (S — it was already ruled in), E3/E4/E5
   membership treatment (M), interim deviation-pin corpus rows for
   E3/E5 (S). Details §3.
5. **(F5) Execution fuel is ruled at the claim level but
   UNREGISTERED at the doctrine level, and `nonterm=` under
   `engine=dedup` is an open claim-standard ruling.** Fuel-out is
   correctly "no verdict, never an observation"
   (`GoLean/GoCore/EnumSpec.lean:20–34`), the differential treats it
   as red, and the enumerator fails loud without `--allow-nonterm` —
   all fail-closed. But the doctrine register's 7 entries do not
   include execution fuel at all, the only decision doc
   (2026-07-18) covers TYPE-RESOLUTION fuel, and `TODO.md:86` +
   charter OQ5 (:610–637) leave "what does `nonterm=` mean under
   dedup" explicitly unruled — with candidate (c) being "a number no
   gate can check" and the wedge row's engine choice riding on it.
   ESCALATE the OQ5 ruling ([USER] claim-shape decision, = M-9);
   REOPEN (S) a register entry for execution fuel. Details §4.

---

## 1. The choice-tape map

### 1a. The machine's choice sites (verified at this tip)

The census of record is code: `ChoiceSite` (State.lean:207–213) +
`ChoiceSite.policy` (State.lean:238–256). All consumption goes through
`Choices.consumeAt`/`consumeAtE` with a site tag; adding a site
without a constructor fails exhaustiveness. Call sites verified:

| Site | Consumption (verified) | Menu/bound source | Empty-stream default |
|---|---|---|---|
| `mapIter` | StepFn.lean:621 | `mapIterCandidates` + conditional stop slot (StepFn.lean:605–633) | first candidate in cell order, stop LAST |
| `appendSpill` | Machine.lean:946 | `appendSpillWidth` (Ops.lean:1968; upper Ops.lean:1964) | gc growth-formula point |
| `l2Entry` | Machine.lean:2802 | ready-clause count (`clauseReady` Machine.lean:1423) | first ready clause |
| `l2Arrival` | Multi.lean:853 | `.multi` outcome count (`arrivalPlan` Multi.lean:844) | first ready clause |
| `l4Waiter` | Multi.lean:1039 | matching candidates (`chanArrivalPlan` Multi.lean:676) | first matched waiter |
| `l1Sched` | Multi.lean:1153 via `Config.boundarySite` (Multi.lean:1099) | `runnableIdxs` (Multi.lean:220) | lowest runnable id |
| `postOp` | Multi.lean:1153 (same line; `.opDone` marker, Machine.lean:2295) | `schedSlots` issuer-first (Multi.lean:1120) | issuer continues |
| `backEdge` | Multi.lean:1153 (same line; loop re-entry shapes) | `schedSlots` current-first | current continues |
| `l5ExitWindow` | Multi.lean:1628 (re-offered per loop entry) | constant 2 | exit now |

Two structural properties that matter for the whole audit:

- **No junk streams.** `Choices.consume` maps every stream value into
  the menu by `c % (max 1 bound)` and realizes the canonical default
  on exhaustion (State.lean:156–160). A `∀ ch` theorem quantifies
  over `List Nat` but the REALIZED behavior set is exactly the menu
  closure — streams cannot make the machine do anything a menu does
  not offer. modeled ⊆ permitted therefore reduces to per-site menu
  correctness (§2).
- **Sequential conservation is a declared policy, not an accident.**
  The width-1 non-consumption of the scheduler-family sites is a
  table entry (`consumeAtOne := false`, State.lean:249–256), with the
  singleton behavior proved (`Choices.consumeAt_le_one`,
  State.lean:292–296).

### 1b. The three-way crosswalk (the lane's core artifact)

Classification key: **DEMONIC** = latitude exercised through the
choice stream; **PINNED** = one deterministic realization, standing
re-envelope debt (includes the inventory's (b-n) narrowed rows —
subset envelopes are pins of the residue); **ARGUED-AWAY** = a
quotient/invariance theorem or recorded observational argument, with
its CONDITIONS named. Rows use the latitude inventory's ids
(`docs/2026-08-11_latitude-inventory.md`); inventory §10's counts
((a) 9, (b) 17, (b-n) 7, (q) 1, REFUSED 9, (d) 6) reconcile with
this table.

| Row | Latitude point | Class | Machine site / record | Debt or condition |
|---|---|---|---|---|
| C1 | which runnable runs next | DEMONIC | `l1Sched`; `runnableIdxs` Multi.lean:220 | maximal only AT registry granularity — granularity residual is ARGUED-AWAY row "reg-gran" below |
| C2 | preemption in boundary-free segment | DEMONIC (at back-edge grain) | `backEdge`; loop re-entry boundaries | sub-statement grain residual → "reg-gran" |
| C3 | post-op effect/continuation interleave | DEMONIC | `postOp`; `.opDone` Machine.lean:2295 | B3 abort window DEFERRED (trigger baseline U-1) — a residual PIN |
| C4 | post-main-exit progress window | DEMONIC | `l5ExitWindow`; execProgLoop Multi.lean:1612–1630 | none beyond granularity |
| C5 | which parked waiter pairs | DEMONIC | `l4Waiter`; chanArrivalPlan Multi.lean:676 | U-2 (L4 ⊆ L1-reach) is [ANALYSIS], no theorem |
| C6 | which ready select clause commits | DEMONIC | `l2Entry` Machine.lean:2802 + `l2Arrival` Multi.lean:853 | "uniform pseudo-random" deliberately possibilistic (support-equal; distributional facts out of scope by declaration) |
| C7 | which clause a WOKEN select commits | PINNED (b-n) + argument | `resumeThread` Multi.lean:402 (head-commit, no draw) | ARGUED by the wake-path coverage argument ([ANALYSIS], envelope-width review): every gc wake outcome realized via prompt-wake L1 schedule. CONDITION: re-argue on any wake-machinery change — recorded, not enforced |
| C8 | sync acquisition order | DEMONIC (via C1, zero new sites) | `applySyncOp` Machine.lean:2015–2043 envelope; wakeReady | contained divergence recorded (RWMutex both-parked successor) |
| C9 | deadlock: detect vs hang | PINNED + argument | `.deadlock` terminal, Multi.lean:1612–; Value.lean latitude note | ARGUED observationally coincident within terminating-run corpus; CONDITION: claims never cite the message/exit-class as semantics (R9/R12 class). Permanent-pin candidate |
| C10 | racy programs | REFUSED (by doctrine) | Race.lean; terminal `raceDetected` | not latitude resolution; soundness of the refusal = Lane A's detector-completeness question |
| C11 | heap address identity | ARGUED-AWAY (q) | `nextAddr` bump; theorem `Frame.allocatorIndependence` — **off-repo, parked branch only** | CONDITIONS: (i) observation surface = pointer equality only; any `%p`/order/`unsafe` channel re-opens; (ii) NEW: theorem no longer in-tree/built — drift unguarded (F1) |
| reg-gran (register #5) | scheduling grain below boundaries | ARGUED-AWAY (incomplete) | NPDRF.lean:31–48 — DRAFT statement, refutable as written; proved mover lemmas cover cross-root class only | CONDITIONS: DRF + an UNPROVED reduction with 6 recorded obstructions (F2) |
| E1 | ordered-evaluation core | FORCED | storeK Machine.lean:1621–, StepFn.lean:610– | n/a (bug class, not latitude) |
| E2 | call vs target operands | PINNED (gc point) | rule-site block Machine.lean:3023–3055 | re-envelope MODERATE-HIGH; five timing pins become membership rows |
| E3 | inter-target operand order | PINNED (OUR point, **known ≠ gc**) | tgtOpK spine; scope clause Machine.lean:3047 | §3 — deviation debt, queue §7 item 5 |
| E4 | targets-vs-RHS panic order | PINNED (OUR point) | tgtOpK→rhsK StepFn.lean:459–500 | rides E3's mechanism |
| E5 | early store across phase boundary | PINNED (spec-literal point; **gc elsewhere**) | two-phase discipline (BUG-032 record) | §3 |
| E6 | len/cap hoist shapes | REFUSED | `panicFreeOperand` | coverage debt, honest |
| E7 | hidden-dep init order | PINNED (go/types point, **known ≠ gc**) | frontend `$pkginit` (init design §1) | §3 — soundness-direction, standing differential red, drift-pinned only |
| E8 | multi-file declaration order | PINNED (b-n, go-command point) | frontend sort.Strings | permanent-record candidate |
| E9 | map iteration order | DEMONIC (full literal envelope) | `mapIter`; candidates/mandatory/stop StepFn.lean:605–633; delete-prune | CONDITION: interpretation I-1/L-012 (recreate = new entry); residual cross-goroutine delete-prune narrowing (a residual PIN, obligation recorded at `Cont.mapIterK`) |
| E10 | ==-equal map key retention | PINNED (always-replace = gc) | Machine.lean:239–243 | LOW; XIMPL-gated |
| E11 | runtime check order in one op | PINNED (gc) | Ops.lean:173–218 etc. | permanent-pin candidate with R9 |
| E12 | binop operand order vs calls | PINNED (structural, frontend ANF) | tools/nativefrontend/wire.go:25 | rides E2; census follow-ons recorded (composite literals, map-literal orders) — NOT yet censused |
| E13 | non-call panic vs sibling calls | PINNED (structural; **known ≠ gc** on assertion axis) | same ANF hoist; NO PIN MAY BE TAKEN | rides E2/E12 membership treatment |
| E14 | receiver vs argument order | census row (class open) | tools/nativefrontend/emit.go method path | F2-class question OWED with E12/E13 |
| R1 | int/uint width | PINNED (64-bit) | `IntKind.bits?` Value.lean:33–34 | §4 — no site-level caveat (inventory §9 flag 2, still true) |
| R2 | append spill capacity | DEMONIC (declared pragmatic subset) | `appendSpill`; envelope [newLen, max(32, 2·growth)] Ops.lean:1940–1968 | deliberately NOT maximal vs spec's unbounded latitude; widen-don't-narrow rule recorded at site |
| R3 | []byte(s) / []rune(s) capacity | PINNED (b-n singleton; **gc known outside**, escaping path) | Machine.lean bytesFromString arm | queue §7 item 4 — best value-per-cost |
| R4 | float fusion / extra precision | PINNED (b-n, per-op rounding) | FloatBits.lean:31–49 | platform-scoped (linux/amd64 GOAMD64=v1); tripwire floats/fma-shape |
| R5 | float div-by-zero panic option | PINNED (b-n no-panic) | Machine.lean:270–275 | permanent-record candidate |
| R6 | out-of-range float→int | REFUSED | Ops.lean:1050–1060 | honest (genuinely target-divergent) |
| R7 | NaN bit patterns | PINNED (b-n canonical NaN) | FloatBits.lean:68–72 | re-decide if `math` lands (would be (q) candidate — needs a theorem it doesn't have) |
| R8 | WaitGroup counter representation | PINNED (gc bit layout) | wgAdd arm (BUG-055) | permanent-pin candidate |
| R9 | panic values/messages | PINNED (gc strings) | Ops.lean/Machine.lean sites | the equality lane's enabling pin; claims never transfer beyond gc |
| R10 | abort-line rendering | PINNED (gc), fail-closed edges | Machine.lean:1373–1443 | BUG-004 fix list is the real obligation |
| R11 | sync misuse fatal class | PINNED (gc throw) | `GoError.fatal` sites | permanent-pin candidate |
| R12 | exit codes / terminal classes | PINNED (harness boundary) | scripts/diff-coverage dispatch | rides R9/R11 |
| R13 | sort stability | PINNED (b-n) + argument | Ops.lean:1931–1947; SortFunc shim genericshim.go:21–24 | ARGUED unobservable for int kinds ONLY; comparator-sort shim ties ARE observable — a live realized-point pin |
| R15 | zero-size address identity | PINNED (never-same singleton; **gc probed non-single-valued**) | fresh `Loc` per var | standing honest RED (escaped-same); may-equal choice or membership row owed |
| R14/U-3 | constant precision extremes | UNKNOWN (delegated) | go/types delegation | open question as stated |
| U-2, U-4, U-5, U-6, U-7 | see inventory §6 | UNKNOWN | — | U-5's one-step wide ops (incl. whole-sort `sortSlice`) are known coarse spots awaiting the granularity re-audit |

Category row counts: **DEMONIC 9** (C1–C6, C8, E9, R2 — 9 entries over
9 sites); **PINNED 24** (17 (b) + 7 (b-n)), of which **5 are
known-≠-oracle** (E3, E5, E7, E13-assertion-axis, R3-escaping — the
honesty-critical subset, inventory §10) and several carry recorded
"permanent-pin candidate" dispositions that the new goal requires
re-arguing rather than inheriting; **ARGUED-AWAY 3 full + 3 partial**
(C11 by theorem (q); reg-gran by DRAFT (incomplete); register #4
SC-in-DRF by literature; partial arguments riding pinned rows: C7,
C9, R13); **FORCED** the §4 list; **REFUSED 9**; **UNKNOWN 5 open**.

Every PINNED row above is a standing debt under the new goal — the
doctrine's own words ("a recorded debt, not a fidelity achievement",
doctrine :70–74). The "permanent-pin candidates" (C9, E8, E10, E11,
R5, R8, R9, R11, R12) were argued permanent under the OLD goal's
cost/benefit ("widening buys no verification value while the oracle
is gc", inventory §7 below-the-line); under the new goal those
arguments must be re-made per Phase-0's rule (a KEEP requires a fresh
argument). My recommended dispositions are in §5.

### 1c. ARGUED-AWAY rows: the conditions, named

1. **C11 allocation addressing (q).** Theorem:
   `Frame.allocatorIndependence` over `execStmtLoop_ren`. Conditions:
   (i) modeled pointer surface is EQUALITY ONLY — `%p`, pointer
   ordering, `unsafe` int↔ptr, or any address-exposing channel
   re-opens the entry (inventory C11's re-opening condition); (ii)
   the theorem quantifies SEQUENTIAL executions (`execStmtLoop`) —
   the concurrent analogue is NPDRF obstruction 1 (allocator
   interleaving does NOT commute up to literal equality,
   NPDRF.lean:54–60), so the quotient does not yet cover pool runs;
   (iii) post-split: the theorem is not in this repo (F1).
2. **Registry-granularity reduction (register #5).** Argument shape:
   Lipton movers / NPDRF (lineage recorded, NPDRF.lean:8–11).
   Status: draft statement REFUTABLE as written; obstructions 1–6
   recorded; only cross-root mover lemmas proved. Condition even at
   completion: DRF, i.e. detector completeness for accepted programs
   (Lane A). Until proved, the honest statement is: registry+backEdge
   granularity is a PIN of the interleaving grain with a planned
   discharge, not an argued-away latitude.
3. **Register #4, SC-only within DRF.** Condition: the DRF-SC promise
   (mem#model, Boehm–Adve pointer) + the refusal boundary being
   TSan's realized edge set, not go_mem's minimal relation (register
   #13) with the U-ledger scoping (U2, U4, U5, O1). The upper-bound
   cost: none (refusal is fail-closed); the C3-relevant residue is
   that REFUSED is load-bearing — a detector FALSE NEGATIVE would
   turn "SC-only" from an argued bound into an invented behavior
   (SC semantics claimed for a racy program whose real behaviors are
   weaker). That soundness question is Lane A's #4; it is a CONDITION
   here.
4. **Partial arguments riding pins:** C7 (wake-outcome coverage,
   [ANALYSIS] — re-argue on wake changes); C9 (observational
   coincidence within terminating corpora); R13 (unobservability
   scoped to int kinds — already breached in spirit by the
   `slices.SortFunc` comparator shim, where ties are observable and
   the machine realizes one member; that half is a plain PIN).

## 2. modeled ⊆ permitted — the direction nobody tests

What the machine offers as evidence, layer by layer:

- **Plumbing totality.** No stream can select an out-of-menu
  behavior (`c % max 1 bound`, State.lean:156–160; exhaustion → the
  canonical member, slot 0, whose meaning is DECLARED per site in
  `ChoiceSite.policy`). So the modeled set at each site is exactly
  the menu closure. Verified: all 8 consumption lines listed in §1a
  route through `consumeAt`/`consumeAtE` with a tag; no raw
  `Choices.consume` call exists in the interpreter outside the
  combinator (grep at this tip; the primitive stays public only for
  the proof layer, State.lean:151–155).
- **Menu correctness per site — the actual locus of the claim.**
  - Spec-SILENT rows (C1, C2, C3, C4, C5, C8): the spec has no
    scheduling text at all (dossier
    `docs/2026-08-20_go-scheduling-semantics-dossier.md:31`), so ANY
    pick among genuinely-runnable goroutines/matching waiters is
    conforming; over-width is only possible via a MENU bug (e.g.
    `runnableIdxs` returning a blocked goroutine — which would also
    break forced blocking semantics and is differentially covered).
    The starvation members are the worked example: spec-permitted,
    gc-never ("eventual scheduling is a strong gc-runtime expectation
    and starvation is treated as a bug, but … the language
    specification allows it", dossier :513–517). These are IN the
    envelope by right (mem#badsync's registry-free-spinner text,
    inventory C2), and the recorded tension (mem model's lone
    "will … at some point" example sentence, dossier :210) is
    documented rather than normalized. VERDICT: the modeled set
    equals the permitted set at registry+backEdge granularity;
    the permitted-⊆-modeled shortfall is the granularity residual
    (F2), not junk width.
  - Spec-CONSTRAINED envelopes — where invention is actually
    possible: **E9** encodes the production table (mandatory = start
    keys never removed must be produced, stop only when none remains,
    created entries produce-or-skip, delete-prune makes
    removed-before-reached exact — StepFn.lean:605–633). Its
    ⊆-permitted argument is conditional on interpretation **I-1**
    (`docs/spec-interpretations.md:30`, [USER]-ruled, ledger L-012):
    if re-created entries were NOT "new", the stop slot could skip
    an entry the spec mandates — the interpretation is the load-
    bearing condition and is properly recorded. **C6**: envelope
    support = the spec's "any that can proceed"; the readiness
    predicate `clauseReady` (Machine.lean:1423) is the menu; its one
    subtle member (send-on-closed counts ready → panic member) is
    probe-pinned (p23). **R2**: any cap ≥ newLen conforms
    (spec §Appending), so the entire [newLen, upper] envelope is
    trivially ⊆ permitted; the containment argument at
    Ops.lean:1940–1963 is about gc-⊆-envelope (the other bound).
    **C4/L5**: "does not wait for other goroutines" licenses any
    finite continuation; the envelope statement additionally argues
    the too-wide side in situ (Multi.lean:1600–1607: window steps
    ride `raceUpdate`, result-cell conflicts refuse).
- **The discipline layer.** "Envelope fidelity is a standing audit
  dimension … reviewers argue each envelope against the evidence its
  statement claims — spec TEXT first — because the too-wide
  direction has no oracle" (nondeterminism doctrine :273–282, with
  the evidence-class duties: every admitted member must conform to
  the quoted sentence; maximality claims must argue why no
  conforming behavior lies outside). This is real and has teeth in
  audit history (the P2 retrofit corrected quote precision across
  the inventory) — but it is a PROCESS guarantee, not an artifact.

**Assessment.** modeled ⊆ permitted is ADEQUATE-by-argument: no
mechanically-checked witness exists or is plausible in general (the
direction has no oracle — correctly diagnosed by the doctrine), but
the argument is localized (per-site, in situ, spec-quoted) and the
plumbing removes the whole junk-stream class. The honest gaps:

- (G1) Menu invariants are not stated as executable checks even
  where they could be (e.g. "every `runnableIdxs` member satisfies
  `threadRunnable`" is definitional, but "no `clauseReady` true on a
  clause the spec calls blocked" and "E9's produced multiset ⊆
  production-table-legal" are checkable per run and are not
  checked). A cheap per-run trace validator over the labeled
  consumption trace (Q2 machinery already exists) would convert the
  audit-only claim into a tested one for every differential run. (S)
- (G2) The SET-equality claim of C3 ("modeled = permitted at every
  latitude point") is currently TRUE only for the spec-silent
  DEMONIC rows at their stated granularity, DELIBERATELY FALSE at
  R2 (declared subset), and false at all 24 pins. Nobody has claimed
  otherwise — the records are honest — but the new goal makes each
  of these a work item, not a caveat (§5).
- (G3) Consumer cost of the too-wide-by-right members: a consumer
  proving `∀ streams` pays for starvation schedules no
  implementation exhibits (fuel-out members, the send-then-spin §5d
  nonterm accounting). That is the doctrine's intended price
  ("weakest machine Go permits"); the mitigation is the liveness
  tier's `Fair : Choices → Prop` (defined set: the four scheduling
  sites, State.lean:204–206), which exists as a DESIGN INTENT only —
  no `Fair` predicate is in the tree. Recorded as owed, not as a
  hole.

## 3. The deviation-debt queue (E3/E5/E7 + hidden-dep-order)

Scope note: "hidden-dep-order" is not a fourth row —
`init/hidden-dep-order` is E7's corpus case. The queue is three axes
(E4 rides E3's mechanism). Findings verified against the dossiers
(`docs/2026-08-15_dossier-e{3,5,7}.md`), `scripts/check-frontend-pins`,
`docs/2026-08-20_w32-re-envelope-charter.md`, and `docs/w32-log.md`.

### E3 (+E4) — inter-target / targets-vs-RHS operand order

- **What deviates:** the machine walks targets left-to-right (the
  `tgtOpK` spine, StepFn.lean:468–495; frontend co-realization
  `tools/nativefrontend/emit.go:2783–2816`); gc's realization is
  compiler-internal and NOT left-to-right (second target's panic on
  the two-target probe, MIDDLE target at three — stable under
  `-N -l`, hence unpinnable; dossier-e3 :31–40). E2's rule-site
  block explicitly disclaims this axis (Machine.lean:3047–3055:
  "the machine's left-to-right is OUR spec-legal realization,
  recorded as OPEN latitude"). Containment fact: divergence cannot
  escape panic SELECTION into side effects (frontend hoists calls
  out of target operands — dossier-e3 :50–53).
- **Re-envelope:** panic-identity membership envelope (admit any
  candidate target's panic; do NOT linearize — dossier
  recommendation, never ruled). MODERATE; shared mechanism with E4.
- **Consumer loss while pinned:** a `∀ streams` theorem quantifies a
  SINGLETON on this axis — it proves "observes panic
  `index out of range [5]`" for programs where gc observes the
  nil-deref. Bounded to panic identity.
- **Guard: NONE.** No corpus case, no baseline row, BUGS.md BUG-032
  `Pinned-by: none` (docs/BUGS.md:1383). A drift in OUR realization
  would be caught by nothing.

### E5 — early store across the phase boundary

- **What deviates:** machine holds phase-1 complete before stores
  (tgtOpK → rhsK → storeK, StepFn.lean:468–500; one-store-per-step
  Machine.lean:1621–1626) — the SPEC-literal point; gc lands the
  early store, and gc's point is STORAGE-CLASS-DEPENDENT (local
  x → 1, package-level x → 0; dossier-e5 :40–45) — "a
  liveness/codegen artifact, not a stable rule". The inverted
  asymmetry (§9 flag 3): here OURS is spec-shaped and gc's exotic.
- **Re-envelope:** two-point store-timing envelope via membership
  ({spec value, early-stored value}), machine keeping the
  spec-literal canonical point — its OWN mechanism (hold the store
  back), riding the E3/E4 slice. Low-if-shared, but a second
  implementation inside one slice.
- **Consumer loss:** wrong VALUES, not just panic identity — a
  theorem proves `x == 0` where a gc run of the same source shows
  `x == 1`, reachable via recover-then-read.
- **Guard: NONE** (probe evidence directory only).

### E7 — hidden-dependency initialization order

- **What deviates:** a FRONTEND pin, not a machine pin —
  `synthesizePkgInit` emits `$pkginit` in go/types' `InitOrder`
  (tools/nativefrontend/emit.go:1282–1312); gc's separate, coarser
  initorder diverges on the spec's own example shape (go/types 4242
  vs gc 4624242, both conforming). Soundness direction: theorems
  over our order do NOT transfer to gc executions of hidden-dep
  programs — ordinary VALUES change.
- **Guard, exactly:** `scripts/check-frontend-pins:42–57` re-runs
  the ONE corpus case end-to-end and byte-diffs the observation
  against `baselines/pins/hidden-dep-order.observation.json`
  (asserts OUR order; drift to any third order caught; ci step 2b).
  The differential row is a permanent expected red
  (`baselines/native-full.tsv:1265`, disposition `latitude`). The
  dossier's own rebuttal names the limit: "the pin only guards the
  ONE corpus case; any user/target program with the shape gets
  silence … that is the definition of fail-open" (dossier-e7
  :113–116).
- **The ruled-but-unshipped interim:** the charter ordered the
  fail-closed hidden-dep detector to ship FIRST (slice 3(a),
  charter :322–325); slice 3 never ran (w32-log :993–995, CARRIED).
  Verified absent: no hidden-dependency/interface-conversion
  reachability check anywhere in `tools/nativefrontend/` (only
  `InitOrder` consumers are emit.go:785/1290/1310 + load.go).
  Knock-on: Q-INITSPAWN's recommended ruling is a rider on slice
  3(a)'s $pkginit surgery — also blocked.
- **Re-envelope:** detector LOW; full envelope MODERATE ($pkginit
  becomes schedule-bearing over the lexical-reference partial
  order's linear extensions). The consumer side condition is already
  written down: "a certificate must carry this as a side condition,
  not prove it away" (`docs/2026-08-21_w7-desugar-inventory.md:1932–1934`).
  North-star exposure: etcd-io/raft has package-level vars.

**Queue-level verdict:** the deviation set is honestly RECORDED and
dishonestly GUARDED — a reader of the charter would wrongly assume
(a) check-frontend-pins covers the queue (it covers one program of
one row), (b) the E7 detector shipped ("ships FIRST" — it did not),
(c) E3/E5 are guarded by something (nothing but prose + probe dirs).

## 4. Idealizations with teeth

### 4a. Fuel

Two distinct fuels; only one has a decision doc.

- **Type-resolution fuel (1024)** — ruled
  (`docs/2026-07-18_totality-fuel-decision.md:59–71`): bounds
  type-NESTING depth, never value size; exhausts as `.unsupported`
  refusal. Benign; KEEP.
- **Execution fuel** — no decision doc of its own. Semantics of
  fuel-out IS ruled at the claim level and it is the right ruling:
  `GoError.fuelOut` is "a MODEL artifact, not a program behavior"
  (Value.lean:159–166); enumeration claims are ∃-fuel-shaped so "a
  divergent branch observes nothing at any fuel" and fuel-out is
  NEVER an observation, member, or evidence of nontermination
  (EnumSpec.lean:20–34); the strict differential lane treats
  fuel-out as red (scripts/diff-coverage:399–402); the enumerator
  fails loud without explicit `--allow-nonterm`
  (CLI.lean:772–775, 908–913); `execProgLoop` classifies
  panic/terminal/deadlock BEFORE the fuel check so a wedged program
  never misreports exhaustion (Multi.lean:1569–1579, throws at
  :1632/:1642). All fail-closed. What is MISSING:
  1. **The register entry.** Execution fuel appears nowhere in the
     doctrine's 7-entry simplifying-assumptions register — the
     claim-level ruling lives only in EnumSpec/Value docstrings.
     Under the new goal, an idealization this load-bearing (every
     harness sentence is ∃-fuel-shaped) should be a named register
     row with its transfer argument (∃-fuel monotonicity) stated
     once. (S)
  2. **The unruled row semantics:** `TODO.md:86` — "RULE what
     `nonterm=` means under `engine=dedup`" — charter OQ5
     (:610–637): under DFS `nonterm=N` is a declared per-branch
     fuel; under dedup a spin is a graph CYCLE cut nowhere, so
     candidate ruling (c) leaves "a number no gate can check";
     riding on it: the membership singleton-guard exemption and the
     send-then-spin wedge row's engine. Deliberately left for
     [USER] (= the doctrine's M-9, "on Mike's desk" —
     nondeterminism-doctrine :145–151; note the duplicate
     identifier OQ5/M-9). ESCALATE.
- **What fuel would falsify if misread:** nothing, today — the
  apparatus is consistently fail-closed. The residual teeth are
  claim-side: `∀ streams` termination claims are FALSE on spinner
  shapes (correctly — spec permits starvation), so termination
  language belongs to the absent `Fair` tier (§2 G3), and a
  consumer who reads a fueled `ok` as "the program terminates on
  all schedules" has made the exact error the possibilistic
  accounting exists to prevent.

### 4b. Unbounded memory / total allocation / empty-heap starts

- **Code reality (verified):** `ExecState.alloc`/`freshLoc` return
  `Loc × ExecState` — no failure mode, `nextAddr : Nat` so no
  address-space exhaustion (State.lean:361–367, :45–46). `makeSlice`
  sign-checks only, then allocates ANY magnitude
  (Machine.lean:757–775); `makeMap` discards the size hint
  (:776–789); nothing models OOM, GOMEMLIMIT, stack limits, or
  gc's `maxAlloc` makeslice panic. Runs start from `heap := []`
  (StepFn.lean:807, :961–983).
- **Register #7's disposition** (doctrine :156–172): STANDING
  IDEALIZATION, no re-envelope obligation, "the too-wide direction
  here does not threaten theorem transfer to real runs that DO
  allocate successfully."
- **Does it survive the new goal? Partially — the recorded argument
  covers only ONE direction.** The too-wide direction (model
  succeeds where real Go would OOM) is indeed transfer-safe, as
  argued. But the machine also FAILS TO CONTAIN a behavior a real,
  arguably conforming Go exhibits: gc's runtime panic on
  over-`maxAlloc` `make` sizes (and OOM aborts generally). For a
  program that does `make([]int, hugeVariable)`, observed (gc:
  runtime panic/abort) ∉ modeled (success) — under the doctrine's
  own bug definition that is a definitional-bug candidate, currently
  absorbed by the register entry's framing rather than by an
  envelope or a refusal. What it would falsify for a wrong-reliant
  consumer: any theorem of the form "this program completes
  normally / prints X" for allocation-heavy programs transfers to
  NO real execution at sufficient scale; the gallery's recorded
  `n < 2^63` domain-condition gloss ("where the MODEL's domain
  ends, never where the program stops working") is the honest
  mitigation and must travel with every such claim.
- **Verdict: ESCALATE (framed choice), not silent KEEP.** The
  standing-idealization label was minted under the old goal.
  Under "everything the standard says Go code might do," an
  implementation-limit allocation failure is plausibly a
  spec-licensed behavior class (run-time panics at implementation
  limits), which would make this a PINNED-to-success singleton at a
  latitude point, not a pure idealization. The [USER] decision:
  (a) KEEP with a fresh argument that explicitly scopes claims to
  successful-allocation runs (cheap; codify the domain-condition
  gloss as a mandatory claim rider), or (b) add a demonic
  allocation-failure member (an `allocFail` choice site — the full
  price register #7 already itemizes and declined). My
  recommendation: (a), recorded as a re-argued KEEP — but the
  argument must be re-made, not inherited.

### 4c. Int width (R1)

- Hard-coded 64: `IntKind.bits?` Value.lean:33–34; `.int`/`.uint`
  are nullary constructors — width is not even a parameter. Recorded
  in inventory R1 (:873–897) and register-extension #6 (:1289–1298)
  — note the extension lives in the INVENTORY's numbering, so the
  doctrine document alone does not carry the int-width idealization.
- **The owed site-level caveat is still missing** — recorded as owed
  since 2026-08-11 (§9 flag 2, repeated at extension #6
  "no site-level caveat yet — owed"); Value.lean:32–42 carries no
  comment. Also entangled: negative-lane acceptance inherits the pin
  via go/types-on-host, and `uintptr` observations are refused.
- What it falsifies: any theorem about wrap/overflow at int
  boundaries transfers only to 64-bit targets; a 32-bit-target
  consumer gets silently wrong arithmetic. Ledger L-014's lesson
  cuts the other way too (gc itself once folded an int constant at
  32 bits — the ORACLE was the wrong side).
- **Verdict: KEEP (fresh argument: no 32-bit oracle exists, XIMPL
  is the gating evidence class — unchanged and still true) +
  REOPEN (S) the site-level caveat, which is a 15-minute debt
  recorded as owed for 20 days.**

### 4d. The owed-rulings queue that touches the envelope

- The **eight Q-rows**: memos written, rulings ALL owed
  (TODO.md:84–85; `docs/2026-08-21_w32-qrow-memos.md` — memos at
  :48/:172/:306/:416/:501/:583/:657/:716, ruling sheet :829–848;
  20 reds riding). CAUTION: charter :648–651 "all eight Q-rows
  ruled" is the DONE-definition, not a status — TODO.md is
  authoritative. ESCALATE (they are [USER] rulings by design).
- **B3 (post-raise abort window)**: DEFERRED at G1 with the U-1
  probe as trigger baseline — but the trigger condition ("an
  observed member needs it") is wired to NO gate and B3 has no
  TODO row; it lives only in inventory C3/U-1 and the doctrine
  residue clause. REOPEN (S): give the trigger an artifact (a
  TODO row + a membership probe that would go red on a B3 member).

## 5. Numbered findings and verdicts

Format per plan Phase 0: KEEP requires a fresh argument; REOPEN
carries S/M/L; ESCALATE is a posed [USER] decision.

1. **C11/register-#6 quotient discharge is an off-repo citation**
   (theorem + design note only at
   `park/reasoning-2026-08-31:proofs/GoLeanProofs/Frame/AllocIndep.lean`;
   this repo's inventory/doctrine cite both). REOPEN (S–M): either
   record the condition explicitly in C11 ("discharge held by the
   reasoning repo against a pinned GoCore version; machine changes
   here re-open the entry until re-proved there") or restate the
   quotient claim as (b-n) with a caveat until the reasoning repo
   exists and pins this one.
2. **Registry-granularity ARGUED-AWAY is an unproved, refutable
   draft** (NPDRF.lean:31–48; obstructions 1–6; only cross-root
   movers proved). KEEP the honest labeling; REOPEN (L) the
   reduction (weakened statement first, per obstruction 4); until
   then C3's grade at this row is WEAK-conditional and every
   concurrency claim's fine-grain transfer is a stated assumption.
3. **modeled ⊆ permitted has no mechanical witness — audit-only.**
   KEEP with the new argument stated in §2 (plumbing totality +
   per-site menus + in-situ spec quotes + the standing audit
   dimension), AND REOPEN (S): a per-run trace validator over the
   labeled consumption trace checking cheap menu invariants (§2
   G1), converting the discipline claim into a tested one on every
   differential run.
4. **E3/E4/E5 are unguarded known-≠-gc pins.** REOPEN: (i) interim
   deviation-pin corpus rows/probes wired like check-frontend-pins
   so OUR realization is drift-caught (S); (ii) the panic-identity
   membership envelope for E3/E4 and the store-timing membership
   for E5 (M, shared slice, two mechanisms).
5. **E7's ruled interim detector never shipped.** REOPEN (S) — the
   charter already ruled it ships FIRST; building it is executing
   an existing ruling, not a new decision. The full E7 envelope
   stays MODERATE, sequenced behind the detector. ESCALATE only if
   slice 3 is to be abandoned rather than rescheduled.
6. **Execution fuel unregistered; `nonterm=` under dedup unruled.**
   REOPEN (S): add the register entry with the ∃-fuel transfer
   argument. ESCALATE: the OQ5/M-9 ruling (three candidates,
   charter :610–637) — it changes what a green membership row
   asserts; also de-duplicate the OQ5/M-9 identifier.
7. **Register #7 (unbounded memory) needs its KEEP re-argued** (§4b)
   — ESCALATE the framed (a)/(b) choice; recommend (a) KEEP with
   the mandatory domain-condition rider codified.
8. **R1 int width**: KEEP (fresh argument stands: no second oracle)
   + REOPEN (S) the 20-days-owed Value.lean site caveat.
9. **The eight Q-rows**: ESCALATE en bloc (memos are ready; 20 reds
   riding; each memo names its recommendation).
10. **B3's trigger is not wired to anything.** REOPEN (S): TODO row
    + trigger probe artifact.
11. **Census-mirror cite drift has no guard and has recurred** —
    the 2026-08-22 re-sync's cites are already stale again
    (`resumeThread` Multi.lean:331→402, `l2Entry`
    Machine.lean:2799→2802, `chanArrivalPlan` 625→676; inventory §0
    mirror). Same failure mode as D2-F1. REOPEN (S): a cite-checker
    (grep-anchored, e.g. "cited symbol appears within N lines of
    cited line") in ci, or move the mirror to symbol-anchored cites.
12. **`Fair` is a design intent, not an artifact** — the scheduling
    sites define its domain (State.lean:204–206) but no predicate
    exists; ∀-stream termination claims on spinner shapes are
    unstatable-as-true until it lands. KEEP as recorded-owed
    (liveness tier), with the §2 G3 consumer note made explicit in
    any claim documentation this repo exports.
13. **The permanent-pin candidates (C9, E8, E10, E11, R5, R8, R9,
    R11, R12) carry old-goal arguments** ("widening buys no
    verification value while the oracle is gc"). Under the new
    goal each needs its fresh KEEP argument; my read: all nine
    survive as version-tracked pins with transfer caveats (their
    observables are message/exit/text-identity classes where an
    envelope dissolves the strict lane's signal for no fidelity
    gain), but the re-argument should be recorded once, in the
    inventory, at Phase-2's devil's-advocate pass.
14. **E12/E13/E14's recorded census follow-ons are open holes in
    the census itself** (composite-literal element order vs calls,
    duplicate-map-key evaluation order, map-literal key-vs-value
    order, receiver-vs-argument F2 sentence — inventory E12
    :771–775, E14). REOPEN (S–M): probe + census rows, same
    treatment as E12/E13 got. This is Lane C's census-completeness
    tie-in: the inventory KNOWS it is incomplete here and says so.

### C3 grade recommendation (input to phase 3)

- modeled ⊆ permitted: **ADEQUATE** (argued, localized, plumbing
  guarantees the stream side; no mechanical witness — F3).
- permitted ⊆ modeled: **WEAK** — honest and enumerated, but 24
  pinned/narrowed rows, 5 known-≠-oracle, the granularity residual
  held by a refutable draft, and the deviation queue's guards
  near-absent (F4). The DEMONIC rows themselves are STRONG at their
  stated granularity.
- The distance is documented with unusual honesty; the gap between
  RECORDS and GUARDS/ARGUMENTS is where the work program should
  point.
