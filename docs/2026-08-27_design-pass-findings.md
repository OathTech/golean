# The whole-project design pass — findings (2026-08-27, professor standard)

Commissioned by [USER] (campaign log, 2026-08-27 entry: "whole-project
design pass, professor-standard — not downscoped; look at
EVERYTHING"). Reviewer: one Fable professor, primary sources only.
Subjects read: the full w1-prover tree @ `20cda772` (proofs +
Audit + logs + design notes), the campaign branch docs @ `0f6017ae`
(plan of record, proof-structure, kill-list, W2.5 note, W3 charter +
Amendment 1, reachability census, the campaign log END TO END), main
@ `84b5edb3` (statement layer, trusted surface, abstract layer), and
the harness/driver sources (`tools/raftsubject/twin-chdriver.go`,
`twin-lib.go`). The prior DIVERGENCE-MAJOR verdict (F1–F5, campaign
log 2026-08-27) is treated as CONFIRMED INPUT — each was re-verified
here from source before being built upon; none was refuted.

Companion deliverable: `docs/2026-08-27_clean-proof-plan-v3-DRAFT.md`
(the refined route, with the priced repair designs). Severities:
**S1** blocks the summit as routed; **S2** must be fixed before the
consuming wave; **S3** owed at the landing ceremony; **S4** hygiene.

---

## Part I — the whole-chain audit (harness sentence → Verdi seam)

Every link: HAVE (verified where, at what generality) / DEFECTIVE
(what exactly) / MISSING (obligation shape + classic ancestor).

| # | link | verdict | evidence and detail |
|---|------|---------|---------------------|
| L1 | **Harness sentences.** `AgreementT1` (partial: ∀ fuel ch r, `twinRun fuel ch = .ok r → r.values[0]? = some (.int 0 .int)`), `CompletionWitness` | **HAVE as Prop** (`Specs/RaftAgreement.lean:59-72`); first-order over `runProgramM`, no accelerator imports — verified by read. **MISSING**: the TOTAL form (`∀ ch, ∃ fuel r, …ok ∧ spec`) and **NeverFaults** (`∀ fuel ch, .ok _ ∨ .error .fuelOut`) exist only as prose in `proof-structure-explained.md` §0 — no Prop, no designation. The [USER] end-state doctrine (log 2026-08-27, "the end-state statement shape") makes the total form THE designated sentence; drafting it is a named unit in v3 (V-S1). Designation itself has NEVER been executed — queued since Arc 1. |
| L2 | **Reflection pair.** `goldenWire%` + `twinLowered` + shape pins + `scripts/check-golden` | **HAVE** (`Specs/WirePin.lean`, `TwinProgram.lean:29-31`, wire sha f353c3b2…, 9,310,086 bytes). The 9.3 MB literal pin remains a tolerated generated-literal scaffold with its recorded retirement route (SpecTec) — labeled, acceptable. |
| L3 | **The glue family** (∃N-total → ∀-fuel partial; truncation classification) | **HAVE, ∀-quantified, pinned** (`RunGlue.lean:423-492`: `runProgramM_mono`, `runProgramM_classify_of_total`, `runProgramM_readout_of_total`; 18 pins in `Audit/W1.lean`). Verified by read: no subject constants. NeverFaults is a ~3-line corollary of the total form + `classify_of_total` — the bridge exists, only the statements are missing (L1). |
| L4 | **Loop rules** (the ∀-iterations dischargers) | **HAVE as rules**: `SliceWalk`, `CondFor` (plain-`for` head, harvested verbatim, witnessed), `mapPickLoop_generic` (element-generic, ∀-draw multiset invariant), `mapPickLoop_perm` (Perm-conservation + tape-suffix). **MISSING**: the one INSTANCE at the driver's source-bounded loop (W4) — blocked on L8/L9/L10. Note: `mapPickLoop_perm` carries its own induction because `mapPickLoop_generic` hides the tape suffix (w3-m finding iii) — the fold-back is a recorded promotion candidate, not yet done. |
| L5 | **Driver body spec** (U3.2e: case analysis over the invariant-constrained net population) | **MISSING**, correctly chartered. Its dependencies: the amended `I` (L8), the composition road (L7), CallSpecV (below), the handler clusters (L6). Verified positive: the driver's pick loop `break`s out of the map-range BEFORE `deliverIdx` (twin-chdriver.go:60-67), so the `Hygiene` clause (`mapIterFree`) is satisfiable at every handler call site — the one structural way the plug premises could have been globally false does not occur. |
| L6 | **Handler/library CallSpecs** (W3.1) | **PARTIAL HAVE**: ~30 exported members across F (log/storage read tier: maybeFirst/LastIndex, maybeTerm ×3, MS first/last/Term ×3, FirstIndex/LastIndex RD walks, rl.first/last, zeroTerm ×3, MustSync member), harvest pair (softState/hardState), init Wave A (6 members incl. ApplySnapshot RD, newLogWithSize), `JointConfig.IDs` at the full (M) family. All ∀-state over reader-vocabulary families, ∀ plans/env/k, ∀ ch, ∃n, count-free exports — spot-verified (`SpecJudgment.lean`, `LogReadSpecs`, `StorageWalkSpecs`, `RaftLogReadSpecs`, `HarvestSpecs`, `InitCallSpecs`, `MapOrderSpecs`). **MISSING**: clusters C/D/E entirely; F's loop-bearing tail (Entries/entries/slice); B's wide members (Ready/acceptReady/Advance); init composition (newRaft chain). Named blockers, all real: **CallSpecV** (function-value call form — see the finding below: it is not merely the confchange closures' need; `raft.Step:1284` dispatches `r.step(r, m)` through a FUNC-VALUE FIELD, so every C/D/E handler consumption crosses a `callValArgsK` site), the `slices.Sort` lowering census (small), (K)/(M) now landed. |
| L7 | **Composition machinery** (spec consumed at a foreign framed site) | **HAVE for the RESULTLESS form only**: CallSpec + FrameSim state half + `callSpan_plug` control half + reader congruence, gated end-to-end at the verbatim stepCandidate call site (`W2Gate.lean`, 38 s). **DEFECTIVE/MISSING for every result-bearing form** (= professor F2, re-verified structurally): `callSpan_plug` is hard-coded to the resultless anchor — `hasBarrierK` recognizes ONLY `.frame [] _ _ _ .stop false` (`Frame/Plug.lean:82-83`), so an R-callee's plans-bearing barrier frame is never matched, and `stepFnIter_plug`'s terminal is pinned `.next .stop` (`PlugRule.lean:95`) while CallSpecR/RD end at `.returning/.next (.frame plans …)`. No transport corollary exists for R-conclusions (`loadMany`/rlocs under ρ). The W3 workers' measured workaround is INLINE re-walk (the maybeTerm precedent) — viable intra-cluster, ruinous at driver scale. The repair design + pricing: v3 §D-B (decision b). Classic ancestor: wp_bind/evaluation-context lift, same as the landed plug. |
| L8 | **The invariant `I`** | **DEFECTIVE** (= professor F1 + F3, re-verified from source, plus three findings of this pass). (i) `ElectedAt.logBridge`/`commitTie` (`Invariant.lean:478-479`) tie the FROZEN S1 carrier to the ADVANCING H-carrier: `EStep` has exactly three constructors (`NativeEtcdDischarge.lean:301-325`); none writes `.committed`, and the only `.log` write is the winner's noop (`specRecvVoteResp`, `NativeObligations.lean:158-159`) — while `HStep.propose`/`leaderCommit` grow `NH`. Falsified at the first Elected-phase propose. (ii) The intended concrete-log↔NH pairing clause DOES NOT EXIST — `deepCommit` pairs the commit/apply axes but no clause pairs concrete log CONTENT with `NH` (and `AbsLog` has no data axis at all — `AbsStateV2.lean:91-98` carries `(index, term)` only, so the full clause is currently UNSTATABLE; a reader extension is part of the repair). (iii) Loop-head QUIESCENCE is not a clause: the landed F/RaftLog specs are stated at the "quiesced family" (empty unstable, live backing — `RaftLogReadSpecs` docstrings) and `shellSync`'s docstring ASSERTS local quiescence, but no conjunct of `I` delivers empty unstable / empty outboxes / drained `stepsOnAdvance` / applied=committed, so the loop rule could never instantiate those specs' preconditions. (iv) NEW (this pass): deleting logBridge leaves the S1 log axes under-constrained for the one place `EStep` still reads them — a delayed MsgVote at a `vote=0 ∧ lead=0` node runs `upToDate` against the frozen `ENode.log`; the square needs a scoped fresh-log clause (design in v3 §D-A). (v) NEW: `ElectedAt.star` fixes `certified := ackCertified voters A.N.ghost tm` at the CURRENT ghost; preservation under ghost growth needs an HStep/Star monotonicity-in-certified transport (easy — `leaderCommitOk` is positive in `certified`, `NativeS23Route.lean:148-150` — but currently absent and unlisted). Repair design: v3 §D-A. |
| L9 | **Init/establishment** | Stage A **HAVE** (`initSetup_establishes`, `InitSpec.lean:95-101`: ∃F₀ ∀fuel≥F₀ ∀ch, entry config + 31 statics, stream-transparent, count-free — verified by read; the ∃-discharge is the charter's sanctioned concrete-evaluation carve-out). Stage B (**the newTwin prefix + newRaft chain → `I` at the loop head**) **MISSING**, parked on (M)-composition + (K) cap families + CallSpecV; the ApplySnapshot slot-0 cap pin is a labeled precondition narrowing whose ∀-ch generalization is owed here. |
| L10 | **Pairing readers** | **HAVE**: `absTwinRead` (fail-closed, TypeId-checked), the U3.0b checker readers (+`absNetMeta`), U3.0d `absProgressOf`/`absRaftLogOf`/`mapReadD`, all with `_ren` congruence + definedness spines. **MISSING** (forced by the L8 repair): a log DATA/TYPE reader (`absLogMeta` — mechanical: `absEntryMeta` exists and composes over storage ents + unstable, `AbsTwinCheckerRead.lean:383`) and a RawNode-shell reader for the quiescence clause (`stepsOnAdvance` emptiness, prevSoft/HardSt sync). Both are U3.0b-class units. |
| L11 | **The abstract layer** | **HAVE, fully ∀, n-generic**: `ElectObligations`/`FullInv.step`/`native_one_leader_per_term`(+cross-time), `etcd_discharges` (all seven members), `HStep`/`HistInv` with the SC1 commit-axis obligations verbatim as constructor premises, `s2_of_histInv`/`s3_of_histInv`/`s23_leaf`, `s1_leaf` via `ClaimTrace` + `violationImpliesDelta`, the model bridges (`s1/s23_viol_delta`, silence lemmas), the four guard shape-pins. Consistency verified in-tree: `I.abs_oneLeaderPerTerm` composes the chain from the pair clause (`Invariant.lean:558-564`). The two retained interface witnesses build-enforced green. |
| L12 | **Checker reshape** (U3.2d) | **MISSING**; the harvest source is real (`s1_span_computes`/`s23_span_computes` on branch campaign-arc4d — byte-closed against the machine readout, wrong-shape as statements, projections `projLOf`/`projBy`/`encGS` reusable). `dataEnc` is `I`'s named joint awaiting exactly this unit. |
| L13 | **W5 seam assembly** | **MISSING** (correctly: it is last). Obligation shapes are pinned by the leaves' premises: `ClaimTrace` (via `ClaimTraceTo.toClaimTrace` — the forgetting map is landed), the checker interfaces, `HistInv`+Star, verdict readout via CheckerCorr.violations + the model-silence lemmas. |
| L14 | **Verdi seam / second dialect** | Post-campaign by plan. The obligation-signature interface (`ElectObligations`, HStep premises) currently has ONE discharging instance (etcd); the Verdi-dialect instance is the recorded vacuity debt — correctly OFF the critical path but must stay on the after-list. |
| L15 | **Trusted surface & gates** | Sound and unmoved: no GoCore/scripts/baselines change anywhere in W1–W3 (verified per-wave in the logs and by `git diff --stat main..w1-prover -- GoLean/ scripts/ baselines/` = imports-only in `proofs/Audit.lean`). The comparator-judge is OWED at the w1-prover merge (Audit.lean moved in W1 and again in W2 — both logs flag it). **DEFECTIVE (S3)**: the ENTIRE W3 wave landed with ZERO Audit pins — no `Audit/W3.lean` exists; `Audit.lean` imports stop at W2. The invariant module, four judgment forms, the crossing kit, MapPerm, and ~30 exported specs are outside the per-theorem axiom-pin discipline (the build's global envelope still covers them, and the workers flagged the lapse rather than hiding it, but the pin gate exists precisely so per-statement axiom sets are inspected at review). |

**Chain verdict.** The top (L1–L3) and bottom (L11) of the chain are
genuinely done and general. The middle is honest, rule-shaped, and
partially built — but BOTH of its two structural joints are broken as
routed: the invariant's Elected phase (L8) and the result-bearing
composition road (L7). Nothing landed is unsound; the defect class is
"the contract the remaining waves would build against is wrong /
absent," caught before any consumer cited it. The v3 route reorders
so both joints are repaired before any cluster spends against them.

---

## Part II — ranked findings

### S1 (block the summit as routed)

**F-1. `ElectedAt` is unpreservable and the concrete↔NH pairing is
absent** (= professor F1, deepened). Evidence: L8 above;
`Invariant.lean:478-479` vs `NativeEtcdDischarge.lean:301-325` and
`NativeS23Chain.lean:100-146`. Deepenings found by this pass, all
part of the repair's scope: the missing DATA AXIS in `AbsLog` (the
full pairing clause is unstatable today); the vote-square fresh-log
sub-clause (the one live post-election reader of `ENode.log`); the
Star-under-ghost-growth transport. The complete clause designs, in
reader vocabulary, are in v3 §D-A. The amendment REOPENS the W2.5
gate — and this time it must be the [USER] gate the plan named: the
defect was introduced under the [AGENT] self-adjudication of that
gate, and the professor's instruction that an [AGENT]-folded repair
would repeat the failure mode stands.

**F-2. The W4 composition road for result-bearing specs does not
exist and was unpriced** (= professor F2, deepened + priced).
Evidence: L7 above. Deepening: the road is needed EARLIER and MORE
OFTEN than the professor's statement implies — `raft.Step` reaches
every handler through the `r.step` func-value field
(raft.go:1284), so C/D/E cluster-internal composition already
crosses `callValArgsK` sites (CallSpecV), and the driver's own
library entries (`rn.Step/HasReady/Ready` — error/bool/struct
results) are R-shaped. Without the road, EVERY composition above the
leaf tier is inline re-walk, whose cost multiplies with call depth
and whose products cannot reuse the leaf-spec investment. Two routes
priced against the measured plug datum (2,948 lines / one session,
W2) and the recorded W1 dead ends in v3 §D-B, with a
recommendation (R-geometry generalization) and an honest
inline-threshold policy for small intra-cluster leaves.

### S2 (fix before the consuming wave)

**F-3. Loop-head quiescence is not a clause of `I`** (= professor
F3). Evidence: L8(iii). The clause design (HasReady-refuting facts,
one conjunct per disjunct of `HasReady`, census E5) + the RawNode
reader extension it needs: v3 §D-A3. Consequence of omission: the W4
loop rule cannot instantiate ANY of the landed quiesced-family spec
preconditions — i.e. the whole F tier would be unconsumable at the
loop head.

**F-4. The `slices.Sort` lowering census and the guard-silence
assignment table are unowned.** The (M) note records that
`slices.Sort` has no lowered body under that name in the wire
(w3-m log, machine finding vi) — `Slice`/`VoterNodes`/`ConfState`
members are blocked on a small census nobody owns. Separately, the
`CheckerCorr.violations` equation makes every one of the 7 harness
guards' silences load-bearing (Invariant.lean:346-348 + joint ledger
item 5), but no unit charter currently OWNS each guard; the T1-V
census routes exist and must be bound to units. v3 carries the
assignment table (§U-ladder, W3.2 column).

**F-5. Small named lemmas absent from every list:** (a)
`HStep`/`Star` monotone in `certified` (L8(v)); (b) the
`mapPickLoop_perm` suffix-clause fold-back into `MapLoops`
(promotion trigger already fired per the ledger's own ≥2 rule —
`mapPickLoop_perm` is the second suffix-needing consumer). Cheap;
listed so they stop being surprises.

### S3 (owed at the landing ceremony)

**F-6. The W3 Audit-pin lapse** (L15). Restore the pin discipline in
one wave: `Audit/W3.lean` pinning the judgment forms' instances, the
invariant sanity lemmas, kit/MapPerm representatives, and every
exported cluster spec (exact axiom trios, in-build). Flagged by the
workers themselves each wave; now overdue.

**F-7. The standing [USER]-review ledger is long and should be
discharged at one ceremony, not dribbled.** Verified list from the
logs: the W2.5 [AGENT] adjudication (subsumed by F-1's gate re-run);
the U3.0d design deltas vs Amendment 1 (`ProgOk.nextUB`, `stateWire`,
`netTerms`-exact, the distributive Next-chain reading — each
individually justified in the clause docstrings; I verified
`nextUB`'s necessity against log.go:401-403 and endorse all four);
the W1 count-bearing-private-lemmas interpretation (endorsed — the
exports are count-free; the reading is the only one under which
harvested walks are usable at all); the W2 ∃-discharge shared replay
+ generator scope note; the 0087b48a cherry-pick lineage (lanes
share the judgment-form commit — merge order accounted); the Term
`i - offset < 2^63` family bound and quiesced-family labels
(endorsed as labeled precondition scopes); the (M) no-pin convention
(= F-6); the judge runs owed.

**F-8. Doc coherence** (mandate 4; the v3 draft is the fix for most
of these): (a) the W2.5 note still carries the five-type population
list, the unsatisfiable `Next ≥ Match+1 ≥ 2` chain, and — root cause
of F-1 — the ambiguous C2 sentence ("the HNet pairing … via the
projection") that U3.0c misread as an S1↔H bridge; the note must be
amended, not just corrected-in-logs. (b) The plan of record's W3
section still says "~15 reachable handlers" vs the census's 172
reachable functions / 6 clusters; its W2.5 line still reads as a
future [USER] gate; its "no unit-count estimate until W1's pilot"
rule has been overtaken by measured actuals. (c)
`proof-structure-explained.md` evidence pins main @ d0e0d2e8
(pre-W0-fix tip; superseded by 84b5edb3) and still calls the loop
family "[PROPOSED]" where CondFor/mapPickLoop landed. (d) The
mechanism registry (`docs/2026-08-26_mechanism-registry.md`, pointed
to by CLAUDE.md as THE index) predates W0–W3 entirely: it indexes
killed modules and omits the judgment family, plug rule, crossing
kit, MapPerm, and the invariant module — a registry refresh is a
named landing-ceremony item. (e) `RaftAgreement.lean`'s docstring
cites `docs/campaign-arc4-log.md` for the T1-V census — present,
verified, no action.

### S4 (hygiene / for the record)

**F-9.** `StmtSpecB`/`CallSpecB` (SpecJudgment.lean:219-234) have
zero consumers. They are cheap definitions, not interfaces, and the
total form MAY not need them (the total sentence needs only ∃-fuel
per iteration + the source-bounded counter + the U3.2c drain bound —
summation of existentials, no uniform B). Keep with a note, or
delete under deletion bias; v3 assumes the ∃n route and names B-forms
only as the fallback if the variant argument turns out to need
uniform bounds.

**F-10.** Forbidden-pattern sweep results: see Part III. Headline:
the landed W1–W3 wave is CLEAN at the export layer (the discipline
held); residual items are labeling/convention-grade, plus one
noteworthy standing tension — canonical-placement addresses (31+) in
precondition FAMILIES are the Sym layer's value-symbolic/
address-concrete design of record, legitimate exactly insofar as the
transport quantifier (`NodePlaced`'s ∃ρ) discharges placement — which
is one more reason F-2's road is structural, not optional.

---

## Part III — the forbidden-pattern sweep

Method: full-file reads of the W1–W3 wave (Part I sources), plus two
read-only breadth scouts (one over the w1-prover wave, one over the
older layers on main); every reported candidate below was re-verified
by me at file:line before inclusion. Findings integrated here.

### III.1 The headline: the export discipline held

Zero live `sorry`/`native_decide` anywhere in `proofs/` (Challenge's
sorry-bodied targets are the judge apparatus, by design); zero
`partial def` outside disclosed meta/tactic code (`Tactics/GoWalk`);
the in-build axiom sweep enforces the classical trio; `kernel_rfl`
is `Eq.refl` + kernel `addDecl` — no native escape. All W3 cluster
exports are count-free with counts confined to `private` span lemmas
(verified by declaration-mapping every literal `stepFnIter <n>` in
the six cluster modules). The reader layer (`AbsTwinCheckerRead`) is
uniformly fail-closed (every catch-all yields `none`; no
`getD`/`default` anywhere in the file). The `{1,2,3}` case list in
`config_validate_callSpecR` and the loop-schema constants in
`SliceWalk`/`MapLoops`/`CondFor` are frontend-desugar shape constants
in ∀-quantified rules — the charter's explicit carve-out.

### III.2 Confirmed sweep findings (each re-verified at file:line)

**P-1 (S3). Vacuous-premise laws survived the kill witness-less —
the non-vacuity gate's own rule is violated by the W0 SURVIVORS.**
The kill-list deleted ALL witness modules as a class (K-B); several
surviving laws' discharge witnesses died with them, leaving
Audit-pinned laws with premises nothing in the tree satisfies:
- `Frame/ChoiceInv.lean:83` `ChoiceInvariantToM` has ZERO
  inhabitants anywhere; both Audit-pinned theorems
  (`choiceInvariant_instance`/`_read`, :107-125) take it as a
  premise; zero consumers exist. The spec route discharges ∀-stream
  directly, so this is legacy. Recommend: DELETE the pair (deletion
  bias; the erasure instrument's statement-former, `ChoiceCanon`,
  can stay) or re-label scaffold with a witness and a date.
- `Specs/Raft/AbsStateV2.lean:287/319/409` — the three `_ren` L4
  transports' witnesses died (in-file admission :46-53). These DO
  have named future consumers (the amended invariant's placement
  clauses); restore witnesses when first consumed, and say so in the
  file now.
- `Specs/Raft/DriverNet.lean:864/1139` — `RebuildInv`/`LiveCountInv`
  have no exhibited satisfying state since `DriverNetWitness` died
  (`Audit/DriverNet.lean:12-16`).
- `Frame/Relocate.lean:69` `frameSim_relocate` — zero consumers, no
  vacuity line, docstring still claims "two named consumers
  recorded" from the killed era.

**P-2 (S3). The stale-docstring class from the W0 kill** — surviving
modules cite deleted artifacts as if live (all verified): `DriverNet.lean:23-25`
(DriverNetWitness), `Frame/ChoiceInv.lean:16-29` (SeedWitness),
`Frame/ChoiceCanon.lean:331-338` (ChoiceCanonWitness),
`NativeCheckerBridge.lean:52-58` (RoundMaLemma/RoundVoteLemma),
`Lens.lean:16/25/503` + `AbsStateV2.lean:72` (LensInst),
`NativeObligations.lean:9-16` ("Nothing here is consumed by any
landed proof" — false: `ElectObligations` is the chain's spine),
`SliceWalk.lean:44-47`, `Sym/SpillTransport.lean:36-39`,
`CondFor.lean:58-63` (names the killed-branch `Sym/UtoaSpan` as a
consumer AND claims "the W2 init spec" consumes it — verified false:
`InitSpec.lean` does not import `CondFor`; its only importers are
the aggregator and `Audit/W2` pins), `AbsTwinRead.lean:9-10`
(retention rationale "the clean proof path states its invariants
over these readers" — true only as of the w1-prover branch; on main
it has zero consumers). Fix: one docstring-batch commit at the
ceremony (schematic tier).

**P-3 (S3). Dead divergent sibling of the plug mechanism.**
`Specs/RaftPilot/Reloc.lean:196-231` `symPlugK`/`symPlugC` — zero
consumers anywhere (verified), no vacuity check, and the barrier
match is WIDER than the real rule's (`| .frame t _te r ds .stop w`
at ANY targets/wrapper flag vs `Frame/Plug.lean`'s
`.frame [] … .stop false`) — a wrapper-transparent barrier is
exactly the unsoundness class the plug premises exclude. Unconsumed
today, hazardous if ever consumed by pattern-matching on the name.
DELETE.

**P-4 (S3). The designated statement set is stale relative to the
doctrine and to the campaign.** `Challenge.lean`/`Audit.lean`'s
designated list (56 names, verified 1:1 with the gate list) contains
NO raft statement — `AgreementT1`/`CompletionWitness` remain
undesignated (queued since Arc 1) — while several designated legacy
entries are pinned-stream/pinned-fuel concrete-run sentences
(`forkJoinStreamCanonical : fjRunGives42 400 [] = true`, etc.).
These are judge kernel-replay targets, a legitimately different role
from proof technique — but the set now mixes gallery-era bounded
witnesses with the trust role the charter assigns to "designated
harness sentences." At the ceremony the [USER] should re-designate:
add TotalT1 (+AgreementT1/NeverFaults), and either re-classify or
retire the gallery rows. (v3 ceremony item.)

**P-5 (S4). Init-cluster singleton families are labeled ∀-state
rules.** `InitCallSpecs.lean` module header claims "∀ σ over the
member's footprint family" while `MPTPre`/`NMSPre`/`ASPre` are
single-state literals (their own local docstrings admit "the
(unique) family member") and several postconditions pin concrete
ALLOCATION addresses (`⟨69⟩`, `⟨91⟩`, `⟨133⟩`, …). For the init
cluster this is legitimate CONTENT — init is the base case, the
config is reflected-program text, and the ∀ plans/env/k/ch
quantifiers are real — but the honest label is "base-case
certificates (∃-discharge class) with parametric
continuation/stream," not ∀-state rules. Relabel in the module
header; no statement change needed.

**P-6 (S4). Scaffolding-label gaps** (contrast: `BfLit`/`BfFixture`/
`SymBase` are exemplary): `CBfLit.lean` (8,011 generated lines) has
no scaffolding/retirement header of its own; `CBfSteps*/CBfSortStep`
labeled but condition-less; `W2Gate.lean` (whole-module fixture
content, honest scope note present) never says "scaffolding" or
names retirement; `Frame/PlugProbe.lean` (tracked probe with live
counts) likewise; `Frame/StepSim.lean`'s module doc is still
"(in progress)". The Bf-era pilot chain also awaits its recorded
retirement (W3 regeneration at the compliant layout) — the fixture
mass (~18k lines across Bf*/CBf*) should carry a deletion trigger
tied to the R-transport gate instance (v3 V-B2).

**P-7 (S4). "PRIVATE" as a docstring word.** The count-bearing
window-link theorems in `BfFixture`/`CBfFixture`/`*Steps*`/
`*SortStep*` are labeled private in prose but are not `private`
declarations, and `BfSortStep`/`CBfSortStep` are enumerated
pick-order case lists (6 leaves each) — inside the labeled
scaffolding tier, consumed only by the pilot spec proofs, so
compliant under the W1 flagged interpretation, but the `private`
keyword costs nothing and would make the boundary mechanical.
Similarly `SymBase.lean:45` `wLogVal`'s `getD .nil` lacks its
sibling's fail-closed justification comment.

**P-8 (S4). Docstring/statement precision nits** (verified):
`LogReadSpecs.lean:576-582` join says "at ANY length n" while the
statement carries the u64/backing-range family bounds (the bounds
are honest reader-vocabulary envelope facts; the docstring should
say "any in-envelope length"); `MapPerm.lean:48-52` counts its "≥2
genuinely different consumers" both inside the single
`MapOrderSpecs` module (the two classes ARE structurally different —
disjoint lemma-inventory halves — but the claim should cite the
classes, not imply two consuming modules);
`NativeEtcdDischarge.lean:527-532` and `NativeS1Chain.lean:129-133`
parentheticals assert the twin's boot state satisfies abstract
premises "trivially" — true only once the seam exists; phrase as
intent, not fact; `s1_leaf`'s "the checker's S1 violation branch
never fires" is a conclusion ABOUT the interface premise (the file's
own header says so; the docstring sentence should carry the
qualifier). `DriverNet.lean:1072-1078/1335-1338` derive their
`67*n+31`/`72*n+31` bounds from "the census's measured iteration" —
the numbers are in fact desugar-anatomy sums (`43 + bB`) and the
docstrings should derive them that way; the statements themselves
are ∀-net-length and compliant.

**P-9 (S4). LINEAGE/quantifier-line coverage is good in the W3 wave,
gappy in the W2-era modules**: `MapLoops` (three loop schemas, no
LINEAGE line), `W2Gate`, `InitSpec`, `Reloc` (no LINEAGE, and see
P-3), the Plug part-files (delegated to `Plug`/`PlugRule`, fine).
One-line headers at the ceremony batch.

**P-10 (S4). Dangling doc pointers from `.lean` prose on main**:
`docs/2026-08-25_campaign-layerc-design.md` (cited by
`NativeObligations.lean:3`) and `docs/2026-08-16_symbolic-domain-design.md`
(cited near `Sym/Drift`) exist on the campaign branch but not on
main — either land the docs or re-point the citations; plus the §P-2
module references. Untracked `artifacts/probe/*` citations in
`SliceWalk`/`DriverNet`/`AbsState` headers are acceptable as
measurement provenance but should be marked "(untracked scratch)"
so an outside auditor knows they are not evidence.

**P-11 (noted, no action).** The nil→zero deref shims
(`derefU64`/`derefBool`/`derefI32`) and the checker-model
`none ⇒ benign` guards (`s1Fires`, `s2Hit`) are deliberate
transcriptions of plainpb getter semantics and of the Go checker
respectively; the transcription's own correctness is exactly what
U3.2d's span-computes-model theorems close (the arc4d SM1/SM2
byte-closures are the harvest source). `ENode.lastIndex/lastTerm`'s
`getD 0` on an empty log is the spec-side empty-log convention,
consistent with `upToDate`'s use. Recorded so the next auditor does
not re-derive the analysis.

### III.3 Sweep verdict

No forbidden-pattern violation of the S1/S2 class exists in the
landed W1–W3 wave: no enumeration stands in for a ∀, no export
carries a subject-run count, no fail-open default sits in a
load-bearing reader. The real debt is the W0 kill's HALF-LIFE — the
witness-less survivors (P-1), the stale docstrings (P-2), the stale
designated set (P-4) — plus labeling hygiene. All are
ceremony-batch-sized; none blocks the route. The two S1 items
(F-1/F-2) remain the only structural blockers, and they were caught
by the calibration review before any consumer cited them — the
process worked; the repairs are designed and priced in the v3 draft.
