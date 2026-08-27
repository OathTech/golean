# The clean proof plan, v3 — DRAFT (2026-08-27, whole-project design pass)

**STATUS: DRAFT, awaiting [USER] adjudication.** The plan of record
remains `docs/2026-08-27_clean-proof-plan.md` (v2) until this draft
is signed off; v2 is deliberately not edited. Companion:
`docs/2026-08-27_design-pass-findings.md` (the ranked findings and
the whole-chain HAVE/DEFECTIVE/MISSING table this route answers).
This document is self-contained: it restates where the campaign
stands, designs the two repairs the DIVERGENCE-MAJOR verdict
demanded, prices the open decisions, and lays the remaining route to
the summit as a unit ladder with quantifier-audit lines and
measured-anchor prices.

## 0. The summit, restated

One designated result shape (the [USER] end-state doctrine,
2026-08-27): the reflection pair + total-correctness sentences about
the pinned twin harness, proved by reasoning:

```
AgreementT1 (partial, pinned):  ∀ fuel ch r, twinRun fuel ch = .ok r → violations(r) = 0
TotalT1 (to be drafted):        ∀ ch, ∃ fuel r, twinRun fuel ch = .ok r ∧ spec r
NeverFaults (to be drafted):    ∀ fuel ch, (∃ r, twinRun fuel ch = .ok r) ∨ twinRun fuel ch = .error .fuelOut
```

Proof method: invariant + loop rule (partial), + variant (total);
NeverFaults is a corollary of TotalT1 via the landed
`runProgramM_classify_of_total`. Then the Verdi-dialect seam
(post-campaign). Designation of the final statement set is [USER]'s
at the landing.

## 1. The quantifier audit (governs every unit; status column new)

| quantifier of the end sentence | discharging rule | status |
|---|---|---|
| subject identity | reflection pair (wire + shape pins) | HAVE |
| ∀ states at spec boundaries | CallSpec family over reader-predicate families (+ crossing kit, (M) carrier) | rules HAVE; ~30 instances landed; clusters C/D/E + composition open |
| ∀ iterations | the loop rule (invariant `I`) | rules HAVE; `I` DEFECTIVE (D-A repairs); instance = W4 |
| ∀ ch — delivery picks | body-spec case analysis over the invariant-constrained net population | MISSING (U3.2e; contract = amended `I`) |
| ∀ ch — latitude draws | choice-site rules ∀-draw + multiset/Perm loop invariants ((K), (M)) | HAVE as rules, exercised |
| ∀ caller contexts (composition) | FrameSim + plug (resultless HAVE); **R-geometry road = decision D-B** | half-HAVE |
| ∃ fuel, r (total form) | source-bounded counter + per-span ∃n + the U3.2c drain measure | glue HAVE; measure MISSING |
| abstract trace facts | [HAVE] native chain, consumed through the invariant's carrier | HAVE (`I.abs_oneLeaderPerTerm` composes) |

No quantifier is discharged by instances. The erasure quotient stays
off the critical path.

## 2. Where the campaign stands (measured, 2026-08-27, w1-prover @ 20cda772)

- **W0** merged (main @ 84b5edb3): the 1.20M-line fixed-trajectory
  era killed; charter rewritten.
- **W1** (1 session): the judgment (`StmtSpec`/`CallSpec`), the
  open-tail finding (continuation-parametricity is kernel-free), the
  glue family (18 pins), the frame verdict (FrameSim alone cannot
  frame foreign call sites → plug rule).
- **W2** (1 session): the plug rule (2,750 lines, ~200-arm walk; §7
  premise census closed: recover + map-range pruning are the ONLY
  context-inspecting features), the loop family, init stage A, the
  compliant-fixture generator; the gate = the exact per-handler
  composition recipe, 38 s.
- **W3 to date** (~5 worker-sessions across 3 lanes, consolidated):
  interface wave (readers, ghost-acks, the invariant module),
  Amendment-1 addenda, the crossing kit (K), the (M) map-order
  carrier + first full-family member, ~30 exported CallSpecR/RD/RN
  members across F/B-start/init clusters. Full build 545 jobs green;
  judge owed at merge.
- **The professor's calibration verdict** at this tip:
  DIVERGENCE-MAJOR — two structural defects (the Elected-phase
  pairing; the unpriced result-bearing composition road), one
  missing clause (quiescence), machinery otherwise sound and
  well-lineaged. This plan's §3 is the adjudication package.

Measured unit costs anchoring every price below (prover logs,
derivation-anchored): straight/pinned-branch member ≈ 30–60 min;
kit-crossing member ≈ 1–2.5 h; 11 members = 1 worker-session;
one mechanism unit (kit, (M), plug) ≈ 0.5–1.5 sessions; a
"session" ≈ one Fable worker-day equivalent.

## 3. THE THREE DECISIONS (for [USER] adjudication)

### D-A. The invariant amendment (repairs F1 + F3; reopens the W2.5 gate as the [USER] gate it was chartered to be)

**A1 — delete** `ElectedAt.logBridge` and `ElectedAt.commitTie`
(`Invariant.lean:478-479`). They equate the frozen S1 carrier's
log/commit axes with the advancing H-carrier; falsified at the first
Elected-phase propose (findings L8). First act of the fix unit: the
mechanized refutation, kept as a regression witness — from any
`ElectedAt` pack, apply `HStep.propose` and derive `False` from
`logBridge` + the fact that no `EStep` from a term-bounded Elected
carrier grows any log (the only log-writing constructor requires a
fresh victory at a term the `terms`/`netTerms` clauses exclude).
Note honestly: the "no EStep grows the log" half is a small lemma
over the three constructors, not a one-liner.

**A2 — add the concrete-log ↔ H-carrier pairing** (the clause U3.0c
was supposed to build; reader vocabulary throughout). New projection
constant (the note's "snapshot index offset absorbed by the
projection", made explicit — abstract hist positions are 1-based
above the harness's index-1 bootstrap snapshot, so concrete index =
abstract index + 1, with the storage dummy entry `(1,1)` at the
concrete head):

```lean
/-- The concrete view of an abstract history: the bootstrap dummy
entry, then the hist entries at the +1 index offset. -/
def hview (H : Hist) : List (Int × Int) :=
  (1, 1) :: H.map (fun e => ((e.1 + 1 : Int), (e.2.1 : Int)))
```

New `ElectedAt` clauses (replacing logBridge/commitTie; `deepCommit`
and `appliedLogs` are KEPT — they are already the commit/apply halves
of the concrete↔NH pairing):

```lean
  /-- Concrete log content pairs with the H-carrier, per node
  (index/term axes; `AbsLog.view` = stable-below-offset ++ unstable). -/
  concLog : ∀ i, i < tv.nodes.length →
    ∀ ra L, absTwinNodeRaft σ tl i = some ra →
      absRaftLogOf σ ra = some L →
      L.view = hview (NH.node (i + 1)).log

  /-- The data/type axes of the same pairing, through the new log
  metadata reader (`absLogMeta`, D-A4) and the `dataEnc` joint:
  positionally, every concrete entry is EntryNormal and its data
  encodes the hist entry's abstract id. -/
  concLogData : ∀ i, i < tv.nodes.length →
    ∀ ra ms, absTwinNodeRaft σ tl i = some ra →
      absLogMeta σ ra = some ms →
      ms.length = ((NH.node (i + 1)).log.length + 1) ∧
      ∀ (kk : Nat) em e, ms[kk + 1]? = some em →
        (NH.node (i + 1)).log[kk]? = some e →
        em.1 = entryNormalTy ∧ dataEnc em.2 e.2.2
```

**A3 — the vote-square fresh-log sub-clause** (new; found by this
pass — the ONE place `EStep` still reads `ENode.log` after the win is
`specRecvVote`'s `upToDate` at a receiver with `vote = 0 ∧ lead = 0`;
for exactly that class the concrete log is provably still the seed,
because accepting an append sets `lead`):

```lean
  /-- Nodes that have neither voted nor learned a leader still hold
  the seed log — what keeps the abstract `upToDate` (over the frozen
  ENode log) and the concrete `isUpToDate` in agreement at the
  delayed-MsgVote square (census R3). -/
  freshLog : ∀ i, i < tv.nodes.length →
    (A.N.node (i + 1)).vote = 0 → (A.N.node (i + 1)).lead = 0 →
    ∀ ra L, absTwinNodeRaft σ tl i = some ra →
      absRaftLogOf σ ra = some L →
      L.view = [(1, 1)] ∧ L.committed = 1
```

The S1 carrier's OTHER frozen axes need no clause: nothing in
`EStep`, `s1Run`, or the leaves reads `ENode.committed`
(verified — the fragment's committed axis lives entirely on the
H-carrier), so it is left honestly unconstrained post-election, with
a docstring saying so.

**A4 — the quiescence sub-clause** (repairs F3; the exact content is
"every disjunct of `HasReady` refuted", census E5 — this is what
makes the landed quiesced-family specs instantiable at loop heads and
gives U3.2c's measure its floor):

```lean
structure NodeQuiesced (σ : ExecState) (tl : Loc) (i : Nat) : Prop where
  logQuiesced : ∀ ra L, absTwinNodeRaft σ tl i = some ra →
    absRaftLogOf σ ra = some L →
    L.unstableEnts = [] ∧ L.applying = L.applied ∧
    L.applied = L.committed
  outboxEmpty : ∀ ra, absTwinNodeRaft σ tl i = some ra →
    absOutbox σ ra "msgs" = some [] ∧
    absOutbox σ ra "msgsAfterAppend" = some []
  shellSynced : -- prevSoftSt/prevHardSt agree with the deep reader
    -- and stepsOnAdvance = [] — via the NEW RawNode-shell reader
    -- (absRawNodeMeta, D-A5)
    ...
```

carried as `Pair.quiesced : ∀ i, i < tv.nodes.length →
NodeQuiesced σ tl i`. Preservation shape: each body-spec case ends
with a harvest pass whose spec CONCLUDES `NodeQuiesced` for the
stepped node (the drain facts already surfacing in the B cluster —
MustSync verdicts, exact softState/hardState readbacks — are this
clause's vocabulary, as the F+B log recorded).

**A5 — the two reader extensions** the clauses need (U3.0b-class,
mechanical): `absLogMeta` (entry `(Type, Data)` down the storage +
unstable chain; `absEntryMeta` exists and composes) and
`absRawNodeMeta` (stepsOnAdvance length + prev{Soft,Hard}St), each
with `_ren` congruence + definedness + a non-vacuity mini-state.

**A6 — the Star-transport lemma** (found by this pass):
`HStep`/`Star` monotone in `certified` (`leaderCommitOk` is positive
in it), so the `ElectedAt.star` at the grown ghost re-validates past
commit steps. ~30 lines beside `NativeS23Chain`.

**Gate:** the amended note (the W2.5 note edited in place with the
amendment section; the five-type population and Next-chain steleness
corrected in the same edit) goes to the [USER] AS THE DESIGN GATE
before any C/D/E charter is issued. Non-negotiable this time: the
original gate's self-adjudication is where F1 entered.

**Price:** refutation + A1–A3 + A6 ≈ 1 session; A4–A5 ≈ 1 session
(two readers + clause + preservation-shape notes). Also the paper
edit of the W2.5 note. Total ≈ 2 sessions before the gate.

### D-B. The result-bearing composition road (repairs F2; the W4 road decision)

The problem (findings L7): a CallSpecR/RD/V proved at canonical
placement cannot be consumed at a framed foreign call site — the
landed plug rule recognizes only the resultless barrier
(`.frame [] … .stop false`) and the `.next .stop` terminal; no
transport corollary exists for result conclusions. Every composition
above the leaf tier currently inlines (window-sum re-walk).

**Route R — R-geometry plug + transport (RECOMMENDED).**
1. Generalize the barrier recognizer + plug clause to plans-bearing
   frames (`.frame ps te r ds .stop false`, any `ps`) and add the
   PREFIX form of the iteration lemma (an in-span `.ok` run whose
   endpoint still `hasBarrier` transports arm-by-arm — the first
   disjunct of the landed `stepFn_plug` iterated). Exit corollaries
   per arrival geometry: R (`.returning (.frame …)`), RD
   (`.next (.frame …)`), V (`callValArgsK` entry — the same barrier
   once entered). Soundness note verified in advance: the barrier's
   `te` slot stays machine-inert THROUGHOUT an R-span because the
   span ends BEFORE the exit arm (the only reader of `te`), and the
   defer-drain arm scrutinizes the targets column but never `te` or
   the tail — the two W2 premises (recover walk, map-range pruning)
   remain the complete non-locality census.
2. The transport corollary `CallSpecR.transport` (and RD/V siblings
   over a shared arrival abbreviation, D-C): FrameSim state half
   (threshold placements ρT — landed) + the generalized plug control
   half + rename transport of the `loadMany`/rlocs conclusion +
   reader congruence. Gate instance: one landed F member
   (`raftLog_firstIndex_callSpecR`) consumed at a REAL caller site at
   a foreign placement — the W2Gate pattern re-run for R.
3. CallSpecV lands here TOGETHER WITH its first consumers
   (`Config.Clone`/`Restore` chain top per the w3-m park record, and
   the `r.step` dispatch site) — the interface-vacuity rule
   satisfied, the serialization rule honored (SpecJudgment moves only
   on the w1-prover lane).

Price against the measured data: the W2 plug class was 2,948 lines /
1 session with probe-first; the generalization reuses the helper
commutations and revisits the ~40 named frame-family cases ⇒
step 1 ≈ 1–1.5 sessions; step 2 ≈ 0.5–1 session; step 3 ≈ 1–1.5
sessions (the w3-m estimate: Clone ≈ 2.5–3× the IDs member). **Total
≈ 3–4 sessions**, and every W3 leaf spec becomes reusable at every
call site.

**Route I — mega-span inline + resultless top transport (NOT
recommended as the road; retained as the small-leaf policy).** Keep
inlining callees into wider walks (the measured maybeTerm pattern);
at the top, restructure the driver body so the only TRANSPORTED spec
is one resultless wrapper per delivery case. Price: inline cost
multiplies with call depth — the driver body inlines
Step-prelude + dispatch + handler + harvest chains per delivery arm
(~10 live arms × F-remainder-class each ⇒ ≥ 10–15 sessions), no leaf
reuse, and every leaf change re-opens every inline copy. The W1/W2
investment in transportable specs is stranded.

**Recommended policy:** Route R as the road; inline REMAINS the
sanctioned technique below a stated threshold (intra-cluster leaves
of ≲2 crossings, where the measured inline cost — additive windows —
undercuts a transport application). This is the middle path with the
threshold written down instead of re-litigated per member.

### D-C. CallSpecV + the judgment-family consolidation

Assessment of the family (CallSpec, CallSpecR, CallSpecRD,
CallSpecRN, + CallSpecV to come): the forms differ in entry
configuration and arrival geometry but share the quantifier
discipline (∀ σ over P; ∀ plans-shape/env/k; ∀ ch; ∃ n; suffix). The
per-form metatheory (`conseq`/`consume`) is 10-line mechanical.

**Recommendation: do NOT build a single parameterized judgment.**
Reasons: (i) each (entry × arrival) combination would have at most
one genuine inhabitant class — a parameterized interface fails the
charter's own vacuity rule; (ii) the forms' quantifier structures
genuinely differ (RD's shaped plans, RN's `targetsPlan` encoding
premise) so the parameterization would carry per-instance side
conditions — a chain in costume; (iii) consolidation would churn ~30
landed spec statements for zero added theorem strength. **Do** take
the cheap unification that has real consumers: a shared
`CallArrival plans env rlocs k : Config → Prop` abbreviation (the
R/RD arrival disjunction — the machine performs the identical next
step from both, per the recorded geometry discovery), so D-B's
transport is stated ONCE over arrivals instead of per form. Revisit
full consolidation only if the family grows past six forms (it should
not: V is the last geometry the machine has).

## 4. The unit ladder (W3 remainder → W4 → W5)

Ordering constraints: **A-wave (D-A) strictly first** (it is the
contract every later postcondition concludes into), D-B parallel to
early clusters (Frame/-tree, file-disjoint), clusters then in
consumer order. One writer per lane; SpecJudgment/Invariant move only
on w1-prover; judge + audit at the single merge ceremony.

| unit | contents | quantifier-audit line | consumers | price (measured anchor) |
|---|---|---|---|---|
| **V-A1** | D-A repair: refutation witness, A1–A3, A6; the W2.5 note amended | interface/contract — advances no quantifier, and says so; the refutation is a regression witness | every W3.2 unit, W4 | 1 session |
| **V-A2** | D-A quiescence + readers (A4–A5) | contract + vocabulary | loop rule (W4), U3.2c, all F-tier consumption | 1 session |
| **V-GATE** | **[USER] W2.5 gate re-run on the amended note** | — | — | user session |
| **V-B1** | D-B step 1: R-geometry plug generalization (+prefix lemma, arrival corollaries) | ∀ caller contexts, by the plug rule (wp_bind lineage) | all cluster composition, U3.2e | 1–1.5 sessions |
| **V-B2** | D-B step 2: `CallSpecR.transport` over `CallArrival` + the R-gate instance | ∀ states at foreign sites, by frame + plug + congruence | same | 0.5–1 session |
| **V-B3** | CallSpecV + first consumers (Clone; the `r.step` dispatch shape) | ∀ states at func-value call sites, by the same judgment discipline | C/D/E, init A composition | 1–1.5 sessions |
| **V-S1** | Statement drafts: `TotalT1`, `NeverFaults` Props + the NeverFaults-from-Total corollary skeleton; POSED for designation | statement layer (trusted); no proof content | W4/W5, the ceremony | 0.5 session |
| **V-F** | F close-out: term/matchTerm/mustCheck transcription tier; Entries/entries/slice with W2 loop rules | ∀ states at log/util boundaries, by CallSpecR + kit + loop rules | C/D/E, checker | 0.5 session + ~2 days (loop tail) |
| **V-Sort** | `slices.Sort` lowering census (small, read-only against the wire) + Slice/VoterNodes members via `sortedLT_eq_of_perm` | census + ∀-state members | C, A | 0.5 session |
| **V-B(harvest)** | B remainder: Resp-message spans, SetHardState, Ready/acceptReady/Advance + unstable accept family; each Q concludes the `NodeQuiesced` drain facts | ∀ states at harvest boundaries; conclusions feed A4's preservation | U3.2c/e/f | 1 session + 2–3 days |
| **V-C** | Election cluster (Step prelude via term-bound; campaign/poll/becomeLeader; Tally/VoteResult via (M)) | ∀ states; ∀ draws via (M)/kit | U3.2a | ≈ F-class (1–2 sessions) |
| **V-D** | Replication cluster (handleAppendEntries 3 exits, maybeAppend/findConflict/commitTo; entry-list loops) | ∀ states; per-arm case analysis = program branch structure | S23 carrier, checker, U3.2e | largest with E (2–3 sessions) |
| **V-E** | Ack/commit cluster (stepLeader MsgAppResp both arms, Inflights, maybeCommit/bcastAppend) | ∀ states | U3.2b | 2–3 sessions, last |
| **V-A(init)** | Init composition: toConfChangeSingle ((K)), confchange chain via (M)+V, newRaft, NewRawNode; ApplySnapshot ∀-cap generalization | ∀ states, ∀ draws (the (M) ∃-out/∀-in threading) | U3.2f | 2–4 days after V-B3 |
| **U3.2a** | Phase transition: the winning MsgVoteResp delivery ESTABLISHES ElectedAt (H₀ = noop-as-first-propose; (ldr,tm) from population) | the Elected base case, by the body-spec case rule | W4 | 1 session |
| **U3.2b** | Match evidence: ghost-acks → `certified` at commit-advance; discharge `leaderCommitOk`; + A6's star transport in anger | abstract premises, by the ack clause | W5 leaves | 0.5–1 session |
| **U3.2c** | Harvest-quiescence measure: the 64-round guard silent via a lexicographic drain measure over the B-cluster drain facts; floor = `NodeQuiesced` | the hardest totality obligation (variant), by loop rule + measure | TotalT1, guard ledger | 1–2 sessions; park-not-weaken clause stands |
| **U3.2d** | Checker reshape over the projections (harvest arc4d `projLOf`/`projBy`/`encGS`; supplies `dataEnc`); concludes C3 fold equations + guard silences | ∀ states at checker spans, by CallSpecs + the model bridges | CheckerCorr preservation, W5 | 1–2 sessions (arc4d harvest de-risks) |
| **U3.2e** | THE DRIVER BODY SPEC: case analysis over the invariant-constrained net population at the pick, symbolic in the net list; concludes I-preservation per case + emissions-preserve-NetCorr + the guard-silence ledger rows | ∀ ch delivery picks (case rule over population); ∀ states | W4 (consumed verbatim) | 2–3 sessions |
| **U3.2f** | Init stage B: newTwin prefix via V-A(init) members; joins stage A; **`I` established at the loop head** (Base complete, the first `I` inhabitant) | the base case (∀-state at entry, by the init spec) | W4 | 1–2 sessions |
| **W4-P** | The loop-rule instance at the driver loop → **the partial sentence proved** (AgreementT1) | ∀ iterations by the loop rule; ∀ fuel by `runProgramM_readout_of_total` | the summit | 1–2 sessions |
| **W4-T** | The variant (source counter + per-span ∃n + U3.2c bound) → **TotalT1**; NeverFaults corollary | ∃ fuel by variant + spec totality | the summit | 1 session |
| **W5** | Seam assembly: ClaimTrace/hlog discharged from CheckerCorr/ElectedAt; leaves fire; verdict readout | abstract trace facts consumed through `I` | AgreementT1/Total/NeverFaults final form | 1–2 sessions |
| **CER** | Ceremony: `Audit/W3+` pin restoration (F-6); mechanism-registry refresh (F-8d); doc re-anchoring (F-8b/c) + the dangling-pointer batch (P-10); the W0 half-life batch — stale docstrings (P-2), witness-less-survivor dispositions (P-1: delete `ChoiceInvariantToM` laws + `Reloc.symPlugK/C`; witness-on-first-consumption notes for the `_ren` transports and DriverNet invariants), init-cluster relabel (P-5), fixture-mass retirement trigger tied to V-B2 (P-6); the designated-set re-designation ask (P-4: add TotalT1/AgreementT1/NeverFaults, reclassify or retire the gallery rows — [USER] act); judge (owed twice over); milestone audit; the [USER]-review ledger (F-7); merge; designation | — | — | 1–1.5 sessions + user ceremony |

**Honest total** at measured velocity: ≈ 20–28 worker-sessions to
AgreementT1 + Total + NeverFaults, sequenced with V-A/V-GATE/V-B as
the strict prefix. The dominant risks, named: (1) `I`-preservation at
U3.2e contact (the first full body case may refute clause shapes —
the W1-pilot pattern says budget one redesign loop); (2) U3.2c's
measure (chartered with an explicit park condition); (3) the R-plug
walk generalization (mitigated by probe-first on two arrival
geometries before the walk is paid, the W2 discipline).

## 5. What the route now contains that it previously did not

(from this pass's own findings — see the findings doc for evidence)

1. The vote-square fresh-log clause and the Star/certified transport
   (D-A3/A6) — absent from every prior list.
2. The log DATA-axis reader (`absLogMeta`) — the full pairing clause
   was unstatable over the landed projections.
3. CallSpecV recognized as a CRITICAL-PATH form (the `r.step`
   func-value dispatch), not merely the confchange closures' need.
4. The guard-silence ASSIGNMENT TABLE: each of the 12 violation
   sites' silences bound to an owning unit (checker sites → U3.2d;
   harvest/drain guards → U3.2c + V-B(harvest); propose-stuck +
   quiescent-without-S4 → U3.2e's case analysis; storage-failure
   guards → V-B members' nil-error conclusions; unexpected-snapshot →
   ProgOk/census §2.4 chain, concluded in V-D/E emissions).
5. The Audit-pin restoration wave and the registry refresh as named
   ceremony items, not ambient debt.
6. The statement-draft unit (V-S1) so designation has artifacts to
   act on — and the designated-set refresh itself (the Challenge list
   contains no raft statement and still carries gallery-era
   pinned-stream rows; findings P-4).
7. The W0 kill's half-life as a batched debt class (findings
   P-1/P-2/P-3): witness-less surviving laws, stale docstrings
   citing deleted modules, and one dead divergent plug sibling —
   dispositions listed in the CER row, so the next audit does not
   rediscover them one at a time.

## 6. Standing rules (unchanged, restated for self-containment)

Charter doctrine governs every unit: quantifier-audit line at
charter-open; LINEAGE for any new mechanism; bounded-technique ban
(exports count-free; scaffolding labeled at birth with retirement
conditions); park-not-weaken; fail-closed; one writer per worktree;
capped builds + box lock; judge at trusted-closure movement; the
audit ask unconditional at the merge; [AGENT]/[USER] provenance.
SpecJudgment.lean and Invariant.lean move only on the w1-prover lane.

## 7. After the summit (unchanged priorities, recorded)

T2 (n-generic harness — the abstract layer is already n-generic; the
harness-quantification design is a [USER] gate), the Verdi-dialect
second instance (the obligation-signature interface's vacuity debt),
the choice-erased symbolic semantics as the post-T1 consolidation
centerpiece (three waiting consumers recorded), the second-target
probe, iris-lean pin refresh before any channel-logic resume.

## 8. Open [USER] decisions collected in one place

1. **D-A**: adopt the invariant amendment (§3.D-A) and re-run the
   W2.5 gate on the amended note — the gate is yours this time.
2. **D-B**: adopt Route R (R-geometry plug + transport) with the
   inline threshold policy; or direct otherwise.
3. **D-C**: keep the concrete judgment family + `CallArrival`
   unification; CallSpecV lands with consumers; no mega-judgment.
4. **V-S1 designation posture**: TotalT1 as THE designated sentence
   with AgreementT1/NeverFaults as decompositions (the recorded
   end-state doctrine) — confirm at drafting, designate at landing.
5. The F-7 review ledger (design deltas, interpretations,
   cherry-pick lineage) — discharge at the merge ceremony.
6. This draft itself: on sign-off it REPLACES v2 as
   `docs/2026-08-27_clean-proof-plan.md`'s successor of record (v2
   archived in place with a supersession banner).
