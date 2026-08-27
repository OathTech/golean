# The whole-project triage plan (2026-08-27) — LAND / KILL / PARK under the architecture of record

**STATUS: PLAN ONLY — nothing executes until [USER] sign-off.**
Commissioned by [USER] (campaign log 2026-08-27, "whole-project
TRIAGE PLANNING PASS"), sharpened mid-pass by [USER] with the
cerberus-lean architecture template and the corpus aim (§7).
Planner: [AGENT] Fable, design-pass worktree. Format model: the W0
kill-list (`docs/2026-08-27_kill-list.md`). Every verdict below is
evidence-anchored (file:line or an import-graph fact verified by
grep, not memory); judgment calls carry [AGENT] tags; uncertainty is
labeled.

**The architecture of record** ([USER], 2026-08-27, after the design
pass; template = cerberus-lean, RefinedC/BRiCk-analogous):

```
  Executable GoCore        — the TCB and statement referent; adequacy
      ⇧ layered              carries proofs down to it
  Relational semantics     — the per-step relation + the language
      ⇧ layered              instance a WP is defined over
  Iris reasoning           — THE BUILD: heap RA, WP, FnSpec
                             contracts, per-construct symbolic rules,
                             assertion layer, case-split, automation
```

Specs are stated and proofs conducted at the Iris tier; the
relational tier carries step rules / lifting; the executable tier is
read out via adequacy + the exec↔relational correspondence. The
CallSpec judgment family is diagnosed parallel-calculus drift;
**CallSpecV and the R-geometry transport road are CANCELLED** ([USER],
recorded in the campaign log 2026-08-27).

**Evidence base** (all read this pass): w1-prover @ `20cda772` (full
delta: 56 files, +39,462/−10 vs main), main @ `84b5edb3` (the Iris
tier, the relational tier, the statement layer, the flagged W0
survivors), the design-pass deliverables @ `69076bc5` (findings
L1–L15/F-1..F-10/P-1..P-11; v3-DRAFT — its unit pricing reused, its
architecture superseded), the campaign log end-to-end, the census
(`campaign/docs/2026-08-27_w31-reachability-census.md`), the parked
lanes (channel-logic, arc4d, ce, wave-a, wp-design, retired arcs),
and `deps/perennial` + `deps/iris-lean` as the boundary reference.

**The headline discovery this triage rests on** (verified from
source, §5): main ALREADY CONTAINS a real three-tier stack. Tier 2
(`Machine.Step`, 155 constructors) has total two-way per-step
correspondence with `stepFn` (`MachineSound.lean:44` `stepFn_sound`,
`:367` `step_complete`, both Audit-pinned) and zero sequential
construct gaps against the raft fragment. Tier 3 is genuine iris-lean
(pinned rev `3877dbec…`, `proofs/lakefile.toml:19-23`): `iProp`,
gen_heap state interpretation (`Ghost.lean:71-75`), a `Language`
instance over `Step` (`Lang.lean:36-49`), the HeapLang-shaped
adequacy family (`Adequacy.lean:83/141/215/280`), ~10.4k lines of
laws, and a designated FuncSpec family proved over REAL etcd-io/raft
quorum functions. The campaign's error was not that the tiers were
missing — it is that the raft lane built a fourth, parallel calculus
(CallSpec over `stepFnIter`) beside them. The triage kills the
parallel calculus, lands its tier-agnostic substrate, and points
everything at the existing stack.

---

## 1. THE LAND LIST

Every item: (a) files, (b) the explicit consumption argument in
tier-2/tier-3-build/corpus terms, (c) landing work. All import
edges verified: **no LAND item imports any KILL item** (import lists
extracted per-file from the branch; the only Audit edges into KILL
territory are the pins pruned at landing, L-14/L-15).

### 1.1 From w1-prover (≈7.7k Lean lines + 3.2k docs)

**L-1. The plug family** — `Frame/{Plug,PlugOps,PlugApply,PlugStep,
PlugRule}.lean` (2,750 lines) + `Frame/PlugProbe.lean` (133).
- *What it is:* `plugK` (`Plug.lean:44`) is a fill function on the
  defunctionalized continuation; `hasBarrierK` (`Plug.lean:82-85`)
  recognizes the resultless barrier; `stepFn_plug`
  (`PlugStep.lean:330`) is the per-step fill/step commutation over
  EVERY arm of `stepFn` (with the complete non-locality census:
  `mapIterFree` + `recoverThroughWrappers` are the only two
  context-inspecting features); `callSpan_plug` (`PlugRule.lean:143`)
  is the span-level bind theorem. Zero CallSpec mentions in any
  statement (grep: docstrings only); imports only `FuelMeasure`.
- *Consumption:* **the bind/frame-entry unit of the tier-3 build
  (G-BIND, §5.3)**. Main's Iris tier has NO `wp_bind` — the `Language`
  instance is bare CEK, "no EctxLanguage" by design (`Lang.lean:43`),
  and every call today goes through per-arity laws
  (`wp_call_enter₁₁/₂₁/₂`, `Laws/Call.lean:84-864`) whose "widening
  owed" notes are explicit (`Laws/Call.lean:471,880`). `plugK` is
  precisely the `fill` such a unit needs, and the plug theorems are
  its commutation obligations — proved once, arm-by-arm, at the
  executable tier whose arms mirror `Step`'s constructors 1:1
  (`MachineSound.lean:4-14`: the two share premise functions
  verbatim, so the relational restatement is case-transport, not
  re-derivation). The W1 probe finding that motivated it (FrameSim
  structurally cannot deliver caller env/k — judgment-design note
  §3) is a durable constraint on any bind design and lands with it.
- *Landing work:* docstring pass on `Plug.lean:9,40` (drop the
  CallSpec anchor phrasing; describe the barrier shape in machine
  vocabulary). `PlugProbe` relabeled: tracked probe/discharge witness
  for the plug premises, judgment-free, **retirement condition = the
  G-BIND unit's own gate instance lands** (replaces the dying
  W2Gate as the plug's non-vacuity demonstration). Audit/W2 pins
  (`stepFn_plug`, `stepFnIter_plug`, `callSpan_plug`) stay.

**L-2. RunGlue** — `RunGlue.lean` (494).
- *What:* fuel monotonicity + truncation classification + the
  ∃N-total ⇒ ∀-fuel-partial readout at the whole-program entry:
  `runProgramM_mono` (`:423`), `runProgramM_classify_of_total`
  (`:446`), `runProgramM_readout_of_total` (`:480`), plus the
  per-phase cascade (`runPkgInitM_*`, `runProgramSetupM_*`).
  CallSpec-free; imports only `FuelMeasure`.
- *Consumption:* **the runProgramM exit theorem (G-EXIT, §5.3)** —
  the missing last step of the adequacy chain. Today's exit doors
  land on `execStmt` (`SurfaceExit.lean:96` `goSpec_of_wp` →
  `Surface.lean:210` `GoTriple`); the designated raft sentences are
  over `runProgramM` (`Specs/RaftAgreement.lean:53-62`). RunGlue is
  exactly the glue that lifts an execStmt/entry-phase result through
  setup + `$pkginit` to the `runProgramM` sentence, and
  `classify_of_total` is the NeverFaults corollary engine (G-STMTS).
  Highest-confidence LAND in the wave. Audit/W1's 18 glue pins stay.

**L-3. The loop-rule family** — `CondFor.lean` (752), the
`MapLoops.lean` delta (+90/−7), `MapPerm.lean` (847).
- *What:* `condFor_loop` (`CondFor.lean:379`) — Floyd/Hoare
  invariant+variant rule for the frontend's cond-only `for` desugar
  over `stepFnIter`, stream-transparent, with in-file witnesses
  (`countdown_span:706`, `cd_concrete:742`). MapLoops delta:
  `mapPickLoop_generic` generalized `List (Int × Nat)` → `List α`
  (conservative; main-side consumers `Examples/Histogram/
  HarnessR.lean:1065`, `Examples/WordFreq/Count.lean:455` keep it
  witnessed) + `mapIter_no_stop_of_unmutated`/`_width_of_unmutated`
  (pick-width facts). `MapPerm`: the (M) carrier — `lookupP_perm`
  (`:140`), `mapPairs_perm` (`:178`), `sortedLT_eq_of_perm` (`:273`),
  the value-generic pick-step family, and `mapPickLoop_perm`
  (`:781`) — Perm-conservation + tape-suffix pick loop. All
  CallSpec-free in statements (MapPerm's five CallSpec mentions are
  docstring narrative, `:33-45`).
- *Consumption:* **the map-range law unit of the tier-3 build
  (G-MAPITER, §5.3)**. Main's `wp_map_iter_inv` is key-only,
  mutation-free, order-silent (`Laws/Range.lean:406-435`, limits
  self-disclosed at `:190-193,403-405`); raft's `for id, pr := range`
  loops and the driver pick loop need key+value binding and a
  Perm-of-draws conclusion. MapPerm's Perm algebra + no-stop width
  facts + the demonic-order treatment are that law's soundness
  content; the executable-tier loop lemmas serve the correspondence
  side and the ∃-fuel discharges (CompletionWitness). `sortedLT_eq_
  of_perm` additionally feeds G-SORT's symbolic `wp_sort_slice`
  packaging.
- *Landing work:* **`mapPickLoop_perm` lands SCAFFOLD-LABELED**: its
  sole discharge instance (`jointConfigIDs_callSpecR`) dies with the
  member corpus (§1.4 — the witness-set ruling); label = "discharge
  witness owed at the G-MAPITER unit; prior discharge archived at
  `archive/callspec-era` (`MapOrderSpecs.lean:864`)". Salvage INTO
  MapPerm: the judgment-free pure lemmas from MapOrderSpecs —
  `idKV_keys:77`, `idKV_filter:83`, `idsFam_population:925`,
  `idsFam_lookup_agree:943`, `idsFam_sorted_collapse:959` (~100
  lines incl. `idKV`) — the order-quotient readback consumer class.
  [AGENT] altitude note, fix optional at landing: `MapPerm.lean:3`
  imports the raft reader module for `mapPairs/mapPairsD`; both land,
  so the edge is legal, but a general kit importing a target module
  is a smell — acceptable now, revisit when G-MAPITER restates it.
  New Audit pin for `mapPickLoop_perm` (currently unpinned — part of
  the F-6 restoration, L-14).

**L-4. The symbolic kit additions** — `Sym/Crossing.lean` (202),
`Sym/ReflectConc.lean` (174).
- *What:* Crossing = ten path-condition step lemmas (branch
  crossings, normalize collapses with literal 2⁶³/2⁶⁴ envelope
  bounds, slice validation, deref/load) over abstract `σ`;
  ReflectConc = the Galois-retraction equations (`reflectK_conc:166`:
  `concK I (reflectK D k) = k` ∀k) for the landed Sym mirror.
- *Consumption:* **case-split machinery for the tier-1/tier-2 proof
  work that the tier-3 build still owes**: every lifting/correspondence
  lemma and every ∃-side discharge (CompletionWitness, reflection
  certificates, G-EXIT's setup facts) is proved by running the
  executable machine symbolically; these are its branch-crossing
  primitives. ReflectConc is an unconditional theorem strengthening
  main's own `Sym/Conc`/`Mirror` (no vacuity exposure).
- *Landing work:* Crossing's three docstring-claimed consumers all
  die (`Crossing.lean:28-33` names three LogReadSpecs members) —
  rewrite the header (consume-on-demand kit; cite the archived
  discharges) and add a ~50-line judgment-free mini-witness at the
  hygiene slice ([AGENT] estimate; a two-branch concrete state
  discharging 3–4 lemmas). Pin representatives in the F-6 wave.

**L-5. The reader vocabulary** — `Specs/Raft/AbsTwinCheckerRead.lean`
(993, new) + the `RenCongr.lean` delta (+81).
- *What:* the fail-closed lens readers (TypeId-checked, `none` on any
  mismatch — re-verified uniform this pass and by the findings sweep),
  each with `_ren` congruence + `Shaped→_defined` + mini-witnesses
  (`wTwin_*:945ff`); RenCongr adds `fieldU64_ren` and
  `absRaftNode_frameSim` (frame-transport of a reader fact).
- *Consumption:* **the pure-projection half of the tier-3 assertion
  layer (G-REPR, §5.3)**. A RefinedC/BRiCk-style assertion layer is
  representation predicates over the heap plus pure projections of
  the represented value; these readers ARE the projections for the
  twin's types, and every Iris-tier raft spec's postcondition speaks
  them (the Surface family's `MeetsSpec` corollaries are the
  existing template: pure `Prop` over read-out values). The `_ren`
  spine is the address-genericity transport until G-REPR's ∃-address
  points-to subsumes it.
- *Landing work:* header line "vocabulary only — advances no
  quantifier" already present (`:42`); add the G-REPR consumption
  note; pin representatives (F-6).

**L-6. The invariant contract, minus its two defective clauses** —
`Specs/RaftPilot/Invariant.lean` (629 → ~620).
- *THE TWO-CLAUSE DELETION LANDS:* `ElectedAt.logBridge`
  (`Invariant.lean:478`) and `ElectedAt.commitTie` (`:479`) are
  deleted at landing — the design-pass F-1 defect (frozen S1 carrier
  tied to the advancing H-carrier; falsified at the first
  Elected-phase propose; re-verified against
  `NativeEtcdDischarge.lean:301-325`). **Replacement clauses (the
  concrete-log↔NH pairing, freshLog, quiescence — v3-DRAFT §D-A) do
  NOT land here**: they are the [USER]-gated W2.5 amendment,
  re-designed at the Iris tier (G-INV, §5.3). No mechanized
  refutation ships with the deletion ([AGENT]: the refutation was
  v3's proposal for an in-place repair; under the architecture reset
  the clauses simply go, and the amendment note records why).
- *What lands:* the clause structure (`Base:140`, `ProgOk:207`,
  `Pair:227`, `CheckerCorr:331`, `NetCorr:382`, `Electing:405`,
  `ElectedNet:432`, `ElectedAt:472` minus two, `Hygiene:494`) + the
  sanity lemmas (`I.abs_oneLeaderPerTerm:558-564` — composes the
  abstract chain from the pair clause). Definitions-only, uninhabited
  by charter (`:36-42`), CallSpec-free, imports
  `AbsTwinCheckerRead` + `NativeCheckerBridge` + `Frame.Plug` (all
  LAND/kept).
- *Consumption:* **the clause inventory of the tier-3 driver-loop
  invariant (G-INV)**. Every clause is a `Prop` over `ExecState` in
  reader vocabulary — at the Iris tier these lift as the pure part
  of the loop invariant (⌜–⌝-embedded, per the `wp_while_inv` /
  `wp_map_iter_inv` pattern) with the heap part supplied by G-REPR.
  The `Hygiene` clause (`mapIterFree`/`recoverThroughWrappers`,
  `:494-496`) is the plug rule's premise pair — the surviving
  consumer edge into L-1. [AGENT] judgment, flagged for [USER]
  confirmation at sign-off: landing an uninhabited contract is
  justified here because the clause design is multi-session
  [USER]-gated work product and G-INV consumes it as its base
  inventory; the alternative (archive-only) re-derives it from the
  archive at G-INV, which the ARCHIVE.md rule forbids without fresh
  justification.
- *Landing work:* the deletion; a header note recording the F-1
  deletion + the pending amendment gate; pin the sanity lemmas (F-6).

**L-7. The abstract-layer deltas** — `Specs/Raft/NativeObligations.lean`
(+55), `NativeEtcdDischarge.lean` (+69), `NativeS1Witness.lean` (+36).
- *What:* the ghost-acks interface (`Ghost.acks`, `ackCertified` +
  monotonicity; self-declared "INTERFACE ONLY … advance no
  quantifier"), the EStep acks-transparency lemmas
  (`EStep_acks_eq`, `ackCertified_estep`), and two non-vacuity
  witnesses (`witness_ackCertified`, `witness_acks_transparent`).
- *Consumption:* the commit-certification premise
  (`HStep.leaderCommit`'s `certified` parameter) that the tier-3
  ack-evidence unit will discharge — the abstract layer (L11 of the
  findings chain) is tier-independent and remains the top of the
  proof; these deltas are its recorded extension, witnessed.
- *Landing work:* none beyond F-6 pins.

**L-8. The init establishment** — `Specs/RaftPilot/InitSpec.lean` (153).
- *What:* `initSetup_establishes` (`:95-101`): ∃F₀ ∀fuel≥F₀ ∀ch, the
  setup phase reaches the entry-frame boundary with the 31 statics
  loaded, count-free, stream-transparent; scaffolding (`initFuel`,
  the kernel replay) kept `private`. Imports RunGlue + TwinProgram +
  KernelRfl only. The ∃-discharge is the charter's sanctioned
  concrete-evaluation carve-out.
- *Consumption:* **the base-case fact of G-EXIT** — the runProgramM
  exit theorem needs exactly this setup-boundary characterization to
  join a WP-at-entry proof to the whole-program sentence. Audit/W2
  pin stays.

**L-9. The prover record** — `docs/{w1,w2,w3,w3-init,w3-m}-prover-log.md`
(2,415 lines), `docs/2026-08-27_{w1-judgment-design,
crossing-kit-design,m-mechanism-design}.md` (794), the
mechanism-registry delta (+12/−1).
- *Consumption:* the record (charter: decisions in tracked files).
  The measured costs in the logs are the pricing anchors for the
  tier-3 unit ladder (the follow-on plan document), and the design
  notes carry the LINEAGE lines for the surviving mechanisms.
- *Landing work:* a supersession banner on the judgment-design note
  (§§1-2,5-6 describe the cancelled calculus; §3's probe findings
  and §7's plug lineage remain live) and on the m-mechanism note's
  CallSpec-threading section. [AGENT] wording at the hygiene slice.

**L-10. Audit** — `Audit/W1.lean`, `Audit/W2.lean`, pruned; the
`Audit.lean` +2 import lines; the `GoLeanProofs.lean` root import
delta, pruned to the LAND set.
- *Prune W1:* keep the 18 RunGlue pins + `reflectV_conc`/
  `reflectK_conc` + `fieldU64_ren`/`absRaftNode_frameSim`; DROP the
  13 SpecJudgment pins + `bfPre_reader`/`becomeFollower_callSpec`/
  `bfPre_inhabited`/`becomeFollower_call_stmtSpec` (subjects die).
- *Prune W2:* keep `condFor_loop`/`countdown_span`/`cd_concrete`,
  the three plug pins, the three MapLoops pins,
  `initSetup_establishes`; DROP `cBecomeFollower_callSpec`/
  `cBfPre_inhabited`/`frameSimG`/`w2_gate` (subjects die).
- *Add (the F-6 restoration, now small):* pins for
  `mapPickLoop_perm` + MapPerm representatives, Crossing
  representatives, AbsTwinCheckerRead representatives, the Invariant
  sanity lemmas, the ghost-acks lemmas — exact axiom trios, in-build.

### 1.2 Already on main — assessed, kept, and now load-bearing under the new architecture

(K-E-style rows: named so the landing ceremony and the registry
refresh treat them as the consumption targets they now are.)

**L-11. The tier-2 stack** — `GoLean/GoCore/Machine.lean` (`Step`
:2821, 155 ctors; `Steps` :3574), `MachineSound.lean` (3,385:
`stepFn_sound:44`, `step_complete:367`, `step_complete_any_wf:2548`,
the terminal-elimination family, wf-preservation),
`Inversions.lean` (`step_det:43`), `Multi{,Sound,WfSound}.lean`
(StepE/StepM + soundness). Zero sorry/partial/native_decide
(verified); pinned (`Audit.lean:548-551,662,1110`). **This IS tier 2
of the architecture of record** — nondeterminism appears demonically
as rule multiplicity (mapIterNext's ∀-idx `Machine.lean:3133`,
append-capacity/select ∃-ch premises), the tape stays below in
`stepFn`, so WP proofs are ∀-schedule by construction.

**L-12. The tier-3 seed** — `Lang.lean`, `LangC/LangD.lean`,
`Ghost.lean`, `HeapBridge.lean`, `Lifting.lean`, `Inversions.lean`,
`Laws/*` (11 files, 6,120 lines over `Step`), `Adequacy.lean`,
`Surface{,Bridge,Exit}.lean`, `Tactics/GoWalk.lean` (10.4k + tactic).
Real iris-lean throughout (§5.1). Kept whole, including LangC/LangD
([AGENT]: their external consumer count is zero beyond Audit —
`GoPrimStepC`/`StepDC` grep — but they are the recorded seam for the
concurrency resume (P-1 park) and are pinned; deleting them would be
churn against a named future consumer. Registry refresh marks them
"post-T1, channel-logic resume seam".)

**L-13. The Surface designated family — the statement idiom of
record** ([USER], this pass). `Challenge.lean`'s designated list:
the golden pin family (goldenTriple/Spec/FuncSpec/Invariant +
readouts + negative twin), recoverFuncSpec (+readout), the quorum
pilots — `quorumOneKnownFuncSpec`(+MeetsSpec/ReturnsTwelve/
NotEleven), `quorumAckedIndexFuncSpec2` (comma-ok, two results),
`quorumThreeAllFuncSpec`(+MeetsSpec/readouts), the Terminates
quartet, the TotalReadout quartet, `committedIndexAllConfigs`
(+family readouts, the ∀-configs form, `committedIndexRef_meets_
spec`) — Iris-stated FnSpecs over REAL etcd-io/raft `quorum` code
with adequacy readouts, negative twins, termination, and total
readout forms. **Presumptively keep-designated; this family is the
existing proof that the FnSpec pattern works at function scale and
the template the raft harness sentences extend** (G-STMTS states
TotalT1/NeverFaults as its whole-program continuation). The
re-designation ask (§4, [USER] act) is therefore SCOPED: it concerns
the gallery-era pinned-stream channel rows (`forkJoinStreamCanonical
: fjRunGives42 400 [] = true` and siblings — judge kernel-replay
targets, a legitimately different role) and the per-seed gallery
total pins (`fib_ok … wordcount_ok` — seed-parameterized, closer to
compliant) — reclassify or retire, [USER]'s call; plus ADDING the
raft statements once drafted. AgreementT1/CompletionWitness
(`Specs/RaftAgreement.lean:59-72`) remain the pinned raft statement
shapes, still undesignated — unchanged by this triage, queued for
the ceremony.

**L-14. Everything else K-E kept** — GoCore + frontend +
differential apparatus (trusted, untouched — verified: the w1-prover
delta touches no `GoLean/`, `scripts/`, `baselines/` file), the
statement layer (WirePin/TwinProgram/RaftAgreement), FastEval +
transfer, `Frame/` core minus Relocate (K-2), `Sym/` core, SliceWalk/
StepKit/FuelMeasure/MapMem/SliceMem/StringMem, Lens, ChoiceCanon
(statement-former; Mask consumed by the parked SpanIso), the
abstract layer, AbsState/AbsStateV2/AbsTwinRead (the `_ren`
transports keep their witness-on-first-consumption note, P-1
disposition), DriverNet (see K-4 note — the two invariant defs are
NOT killable), the Examples gallery + GooseParity/Imported sets
(now ALSO the corpus seed pool, §7).

### 1.3 The two-clause invariant deletion

Included above as L-6 — restated as its own row because the brief
requires it explicitly: **`ElectedAt.logBridge` and
`ElectedAt.commitTie` (`Invariant.lean:478-479`) are deleted in the
landing branch's hygiene slice; the replacement clauses wait for the
[USER]-gated amendment (G-INV), re-designed for the Iris tier.**

### 1.4 The minimal-witness ruling (the CallSpec carve-out)

**[AGENT] answer: ZERO CallSpec members survive on main.**
`SpecJudgment.lean` dies whole. The mechanisms the members witnessed
are covered judgment-free:

| mechanism | non-vacuity after the kill | evidence |
|---|---|---|
| plug (L-1) | `PlugProbe.lean` — judgment-free, already discharges the plug premises on a concrete program; relabeled with a G-BIND retirement condition | imports `Frame.Plug` + `Sym.KernelRfl` only |
| condFor (L-3) | in-file `countdown_span`/`cd_concrete` | `CondFor.lean:706,742` |
| mapPickLoop_generic (L-3) | main-side consumers Histogram/WordFreq | `Examples/Histogram/HarnessR.lean:1065`, `Examples/WordFreq/Count.lean:455` |
| mapPickLoop_perm (L-3) | **scaffold-labeled at landing**; witness owed at G-MAPITER; prior discharge cited to `archive/callspec-era` (`MapOrderSpecs.lean:864`) | §1.1 L-3 |
| crossing kit (L-4) | new ~50-line judgment-free mini-witness at the hygiene slice | §1.1 L-4 |
| ReflectConc (L-4) | unconditional equations — no premise to witness | `ReflectConc.lean:166` |

*The priced alternative, recommended against:* retaining one live
member per mechanism would keep `jointConfigIDs_callSpecR` + its
closure (`MapOrderSpecs` 992 + `SymBase` 96 + `SpecJudgment` 483 ≈
1,571 lines) and one kit member (`LogReadSpecs` slice, ~500+ lines
after trimming) — i.e. the dead calculus stays in-build, in the
axiom-pin surface, and in every future auditor's reading list, to
witness mechanisms that have cheaper honest witnesses. This repeats
the W0 half-life pattern (P-1) in the opposite direction. The
scaffold-label route is the doctrine's own device (label at birth,
named retirement), applied with a recorded prior discharge —
strictly more honest than P-1's silent witness-loss because it is
labeled and dated at landing. **[USER] call at sign-off if a live
witness is preferred despite the price.**

---

## 2. THE KILL LIST

Mechanism: nothing is lost to history — `archive/callspec-era` pins
the w1-prover tip (§4). "Importers checked" = the import-graph fact
that nothing on the LAND list imports the item (extracted per-file;
the two Audit files' pruned sections are the only edges, removed in
the same commit).

### 2.1 The parallel calculus (w1-prover; never lands) — ≈28.4k lines

**K-1a. `SpecJudgment.lean` (483).** The six judgment forms
(StmtSpec/CallSpec/R/RD/RN + B-forms) + per-form conseq/consume +
seqn/call rules + sealed refusals. Off track by [USER] diagnosis:
a continuation-parametric triple calculus over `stepFnIter` is a
parallel WP — the Iris tier already has the real one. The B-forms
additionally had zero consumers (findings F-9). Importers: only the
member/pilot files below + Audit/W1's pruned section. *Re-derive
later:* nothing — FnSpec contracts at tier 3 are the replacement
(the Surface family is the working template).

**K-1b. The member corpus (8,569 − ~100 salvage):**
`Specs/RaftPilot/LogReadSpecs.lean` (2,389),
`StorageWalkSpecs.lean` (1,706), `RaftLogReadSpecs.lean` (1,507),
`InitCallSpecs.lean` (1,323), `MapOrderSpecs.lean` (992, minus the
§1.1 L-3 salvage), `HarvestSpecs.lean` (652). ~30 CallSpec members.
Two independent kill grounds: (i) the form is cancelled; (ii) the
preconditions are single-state fixture families with literal
addresses baked into statements (`UFIPre` `LogReadSpecs.lean:165`,
`IDsPre` `MapOrderSpecs.lean:192`, receiver `⟨31⟩`, results
`⟨33⟩/⟨34⟩/⟨35⟩` — verified by the module scout), i.e.
precondition-narrowed base certificates, not the ∀-state rules their
headers claim (findings P-5 generalizes). Importers: each other +
the pilots + `GoLeanProofs.lean` root; nothing on LAND. *Re-derive
later:* the CONCLUSIONS' semantic content — exact readbacks of the
log/storage/harvest/init functions in reader vocabulary — is real
and re-derives as tier-3 FnSpec postconditions at the cluster units;
the archive is the reference (per-member windows, crossing maps, and
measured costs in the w3 logs, which LAND).

**K-1c. The pilot/gate chain (925):** `BecomeFollowerSpec.lean`
(262), `CBecomeFollowerSpec.lean` (207), `CallSiteComposition.lean`
(140), `W2Gate.lean` (316). The W2 composition demonstration. Its
load-bearing content — `callSpan_plug` + `absRaftNode_frameSim` —
lands via L-1/L-5; the CallSpec wrapper being transported dies.
**Cost accepted ([USER] flag at sign-off):** the tree temporarily
loses its only end-to-end framed-composition demonstration; the
G-BIND unit's gate instance is the named replacement, and PlugProbe
covers plug non-vacuity meanwhile. Importers: Audit/W1+W2 pruned
sections only.

**K-1d. The fixture mass (18,270 + 296 tool):** `SymBase`, `BfLit`
(7,890 generated), `BfFixture`, `BfSteps`, `BfSteps2`, `BfSortStep`,
`CBfLit` (8,011 generated), `CBfFixture`, `CBfSteps`, `CBfSteps2`,
`CBfSortStep`, `Reloc` — plus `tools/relayout/CBfLitGen.lean`. All
scaffolding-labeled at birth (verified per-file); their retirement
condition (a compliant-layout regeneration for W3) is mooted by the
architecture reset. **Includes `Reloc.symPlugK/symPlugC`
(`Reloc.lean:196,231`)** — the dead divergent plug sibling (P-3):
barrier arm `.frame t _te r ds .stop w` at ANY targets/wrapper flag,
wider than the real rule's `[]`/`false` (verified side-by-side with
`Plug.lean:83`) — the exact unsoundness class the plug premises
exclude, unconsumed, deleted with prejudice. Importers: the pilot
chain only. *Re-derive:* nothing; the Bf-era findings live in the
landed w1/w2 logs.

### 2.2 Main-side kills (small, surgical) — ≈260 lines

**K-2. `Frame/Relocate.lean` (122) — whole module.** Zero live
consumers verified: `frameSim_relocate` grep = nothing;
`span_relocate` grep = only its `Audit/Kit.lean:751-752` pin;
`renameHeap`/`renameState` grep = in-file only. Docstring claims
"two named consumers recorded" from the killed era (P-1, verified
false). Its role — address-relocation transport — was the cancelled
R-geometry road's vocabulary; at the Iris tier, placement
genericity is the assertion layer's job (∃-address points-to,
G-REPR). Deletion: module + root import + the Audit/Kit pin pair.
*Re-derive:* nothing (Frame/Rename/RenameId — the consumed renaming
modules — are untouched; RenCongr's imports verified:
`Frame.Transfer`, `Frame.RenameId`, not Relocate).

**K-3. `Frame/ChoiceInv.lean` (127) — whole module + its pins.**
`ChoiceInvariantToM` (`:83`): zero inhabitants, zero consumers
anywhere (verified: importers = root + `Audit/ChoiceInv.lean` only);
both pinned theorems (`choiceInvariant_instance:107`,
`choiceInvariant_read:116`) take it as a premise; the in-module
`anchorRun` defs have no external consumers. The spec route
discharges ∀-stream directly (P-1's own analysis); the erasure
instrument's statement-former (`ChoiceCanon`, 607 lines) STAYS
(K-E; `Mask` is consumed by the parked SpanIso). Deletion: module +
root import + `Audit/ChoiceInv.lean`'s two pins (`:45-49`; the
file's ChoiceCanon pins stay — verified separable). *Re-derive:*
if the choice-erasure consolidation (post-T1, §3 P-3) needs an
invariant-transport form, it re-derives against SpanIso's relation
with a witness, per the ARCHIVE.md rule.

**K-4. NOT killed, recorded to close the P-1 row:**
`DriverNet.RebuildInv/LiveCountInv` — the design pass listed them as
witness-less survivors; import-graph check this pass shows they are
the loop-invariant PARAMETERS of the KEPT ∀-span lemmas
(`DriverNet.lean:901,909` — `rebuildLoop_span` concludes/consumes
them), so deletion would break K-E keeps. Disposition: the P-2
docstring fix + a witness-on-first-consumption note, at the hygiene
slice. Likewise AbsStateV2's three `_ren` transports: keep, with the
note (named future consumer = G-INV's placement clauses).

### 2.3 Hygiene deletions folded into the landing (not separately ceremonied)

**K-5. The stale-docstring batch (P-2, ~12 files, verified by grep
this pass):** `DriverNet.lean:23-25`, `Frame/ChoiceCanon.lean:
331-338`, `Lens.lean:16/25/503`, `AbsStateV2.lean:72`,
`NativeCheckerBridge.lean:52-58`, `NativeObligations.lean:9-16`
(claims "nothing here is consumed" — false since the invariant),
`SliceWalk.lean:44-47`, `Sym/SpillTransport.lean:36-39`,
`CondFor.lean:58-63` (false consumer claim, comes in with L-3),
`AbsTwinRead.lean:9-10`, plus the L-9 supersession banners. One
docstring-batch commit, schematic tier.

**K-6. Dangling doc pointers (P-10):** `NativeObligations.lean:3`
cites `docs/2026-08-25_campaign-layerc-design.md` (campaign branch
only) and `Sym/Drift` cites `docs/2026-08-16_symbolic-domain-design.md`
(wp-design branch only) — resolved by LANDING both docs (the second
also closes the wp-design lane, §3 P-4); `artifacts/probe/*`
citations get "(untracked scratch)" markers.

---

## 3. THE PARK LIST

Only items with a NAMED resume condition. Every park = branch ref
kept + worktree pruned + an ARCHIVE.md (or registry) row; the
standing rule applies (nothing archived is ever cited by a proof).

**P-1. channel-logic** — refs `channel-logic` @ `f49752a6` (+
`channel-logic-s1..s4`; s4 @ `9fbf674d` NEVER merges as-is — its
citable target was refuted, branch record). 14,542 lines: a fourth
`Language` instance (`LangDM.lean:515`, cell-mediated pool dialect)
+ 46 DM law ports + channel invariant/resource tiers + specs.
- *Where it sits under the new architecture:* genuinely tier-3 work
  — it builds ON the surviving Lang/Laws layer (verified: zero
  killed-module dependencies; 3 textual conflicts only). It is the
  concurrency wing of THE BUILD, out of T1 scope (the census: the
  fragment is single-goroutine, zero channels).
- *Resume condition (named):* the post-T1 concurrency arc, gated on
  (i) the iris-lean pin refresh (standing [USER] backlog item),
  (ii) the machine re-envelope its own charter names
  (charter §285-312), (iii) a G-REPR-shaped channel assertion
  design. Salvage risk **HIGH**: merge-base `ba6398ab`, 841 commits
  behind; `StepDM` hand-transcribes the machine step, so 6.8k lines
  of GoCore drift land directly on it — expect selective
  re-derivation (laws and design notes salvage; the dialect
  transcription likely rebuilt). The channel-logic rot lesson is
  the reason THIS plan parks almost nothing else.

**P-2. campaign-arc4d** — ref @ `7fa0e04d`. The span theorems
(`s1_span_computes` `SpanS1Walk.lean:541`, `s23_span_computes`
`SpanS23.lean:133` — wrong-shape as statements, harvest-only) + the
projection triple `projLOf`/`projBy`/`encGS` + commutations
(~1,470 lines, verified free of the one killed import that blocks
the span files).
- *Resume condition:* consumed at the checker-model unit of the
  tier-3 build (the `dataEnc` joint and the checker fold equations —
  U3.2d's successor). Salvage risk LOW for the projections (lift
  cleanly), MODERATE for the span content (byte-closure evidence
  only).

**P-3. campaign-ce (SpanIso)** — ref @ `a1d70861`. The choice-
erasure relation + 52 phase-1 adequacy theorems + witnesses; the
CE1 iff unbuilt; depends on two W0-deleted witness files.
- *Resume condition:* the post-T1 choice-erased-semantics
  consolidation (the recorded three-consumer item). Salvage risk
  MODERATE (self-contained definitions; witness files re-derivable).

**P-4. wp-design** — ref @ `c3dc3986`. Resolved by LANDING its one
unmerged artifact (`docs/2026-08-16_symbolic-domain-design.md`, 901
lines, carries the [USER]-ruled OQ3 embedding-mediated drift
equation + a live charter-amendment TODO) in the landing branch's
doc slice, then retiring the lane. Not a park — a landing plus a
prune. The charter-amendment TODO (the literal `stepFn' @ GoValue =
stepFn` phrasing → the embedding form) is a named hygiene item.

**P-5. Retired outright (prune worktrees; refs per note):**
`w0-reset` (byte-identical to main — duplicate), `launch-fixes`,
`campaign-arc2/3/4b/4c` (all MERGED — refs deletable at [USER]
pleasure), `campaign-arc4` (MERGED; ref shared with
`archive/fixed-trajectory-era` @ `c4986b29` — keep the archive name,
the arc name is deletable), `campaign-wave-a` @ `b3c329c8`
(UNMERGED but 10/12 files superseded by the W0 kill; ARCHIVE.md:73-74
already records it — keep the ref, prune the worktree), `w1-prover`
(pruned AFTER `archive/callspec-era` is cut and the landing branch
merges). The `campaign` worktree STAYS (the live log lane, 161
commits of record). `design-pass` stays until its deliverables'
disposition is ruled at the ceremony.

---

## 4. THE MECHANISM

**Archive refs.**
- `archive/callspec-era` = branch ref at `20cda772` (the w1-prover
  tip) — the judgment family, the ~30 members with their exact
  readback conclusions and measured windows, the pilot chain, the
  fixture mass. ARCHIVE.md gains its section: what lived there, the
  lesson (parallel-calculus drift: leaf specs stated in a bespoke
  triple calculus over the executable machine while a real Iris tier
  stood on main), and the harvest pointers (member conclusions →
  tier-3 FnSpec postconditions; window/crossing maps → cluster-unit
  pricing).
- Existing `archive/fixed-trajectory-era` @ `c4986b29` unchanged.
- Park refs (P-1..P-3) are already branch refs; ARCHIVE.md rows for
  channel-logic (new) and the two campaign harvests (rows exist,
  updated with the resume conditions above).

**The landing branch.** `triage-landing`, created AT `20cda772`
(w1-prover is main + 56 files, merge-base = main tip — verified by
the −10-deletion diff), so history stays legible as deletions on a
working branch, exactly the W0 mechanism. Commit sequence (each a
reviewable slice):
1. K-1 deletions (SpecJudgment, members minus salvage, pilots,
   fixtures, CBfLitGen) + root-import and Audit/W1+W2 prunes + the
   MapOrderSpecs→MapPerm salvage move.
2. L-6 two-clause invariant deletion (its own commit — the F-1
   record cites it).
3. Main-side kills K-2/K-3 (+ pin prunes).
4. The hygiene batch: K-5 docstrings, L-1/L-3/L-4 relabels +
   scaffold labels, the Crossing mini-witness, L-9 supersession
   banners, K-6 doc landings (symbolic-domain + layerc notes),
   ARCHIVE.md sections, mechanism-registry refresh (F-8d: index the
   landed plug/kit/(M)/readers/invariant; deindex the killed
   judgment; mark LangC/D's resume seam).
5. The F-6 pin-restoration wave (Audit additions for the previously
   unpinned LAND items).

**The ceremony (exact, per the merge protocol):**
1. `scripts/ci` on the landing branch — via `scripts/capped`,
   `GOLEAN_MEM_MAX=48G`, box-wide build-lock protocol
   (`docs/operational-lessons.md`), sequential warm first (the
   interface-hot Audit/root edits owe it). Docs-only sub-slices ride
   the same gate.
2. `scripts/comparator-judge` — **owed and triggered thrice over**:
   Audit.lean moved at W1 and W2 (both logs flag the judge as owed)
   and moves again here (pin prunes = trusted-closure movement). One
   landmark run at the branch tip covers, per the widened 2026-08-22
   trigger. Anchor: the last landmark ran 742 s / 56 theorems
   (main log @ `118d31aa`); the designated list is UNCHANGED by this
   landing (no designation act occurs on the branch), so the run is
   like-for-like.
3. The pre-merge adversarial audit ask — unconditional; scope
   proposal: (i) the kill boundary (nothing landed imports the
   dead), (ii) the two-clause deletion's blast radius, (iii) the
   relabel honesty (scaffold labels vs the witness ruling §1.4),
   (iv) trust surface untouched. Reviewers Opus, per standing rule.
4. The standing [USER]-review ledger (findings F-7) discharged at
   the same ceremony, not dribbled.
5. Pause; merge on explicit at-that-moment sign-off:
   `git checkout main && git merge --ff-only triage-landing`.
6. The designation acts (L-13 scope: gallery-row reclassification;
   raft statements POSED once G-STMTS drafts them) — [USER], at or
   after the ceremony; a judge re-run follows any designation change.
7. Worktree prunes (P-5) after the merge; end parked on main, clean,
   green. Push is its own sign-off, as always.

**Branch topology after:** `main` (landed) · `archive/
fixed-trajectory-era` · `archive/callspec-era` · parks:
`channel-logic`(+s1..s4), `campaign-arc4d`, `campaign-ce`,
`campaign-wave-a` (harvest-noted) · live lanes: `campaign` (log),
`design-pass` (until ruled). Worktrees: `campaign`, `design-pass`,
primary on `main` — all others pruned.

**Post-landing main contains:** the three-tier stack (GoCore + the
relation/correspondence + the iris-lean tier with the Surface
FuncSpec family designated), the landed substrate (plug, glue, loop
rules + (M), kit, readers, the amended-pending invariant contract,
init stage A, ghost-acks, the prover record), the differential/
corpus apparatus, the gallery (now the corpus seed pool), zero
CallSpec artifacts, zero known witness-less laws (all either
witnessed or scaffold-labeled with dates), a refreshed registry, and
a designated set whose refresh is a queued [USER] act.

---

## 5. THE TIER-3 BUILD INVENTORY (the gap table, in the [USER]'s BRiCk-analogous terms)

What exists vs what the raft fragment demands, per build category.
Source: the tier scouts' file:line-anchored reads, spot-verified;
census demands from `2026-08-27_w31-reachability-census.md` (the
fragment is single-goroutine, no channels; its one live choice site
is the driver's map-range pick).

### 5.1 HAVE (verified, on main)

| category | status | evidence |
|---|---|---|
| **Heap RA / state interp** | REAL: gen_heap over base-address cells + pinned prog/methods/types purity; concrete camera bundle (HeapLang `heapΣ` shape) | `Ghost.lean:32-80`, `Adequacy.lean:36-61` |
| **WP** | iris-lean `WP` over `Step` via the bare `Language` instance; fancy updates, later credits, Löb, invariants all real | `Lang.lean:36-49`; `Laws/Loop.lean:95`; `SurfaceExit.lean:149` |
| **Tier-2 relation + correspondence** | 155-ctor `Step` + `Steps`; `stepFn_sound`/`step_complete` TOTAL both directions per-step; `step_det` on the choiceFree core; StepE/StepM concurrency relations; all pinned; **zero sequential construct gaps vs the census** (map-range demonic pick, sync-in-stmt-position, defer/panic/recover, func-value calls, all `stmtPlan`/`strictPlan` ops covered) | `Machine.lean:2821-3572`; `MachineSound.lean:44,367,2548`; `Inversions.lean:43`; scout table §3, re-checked vs census |
| **FnSpec contracts** | `GoFuncSpec` (`Surface.lean:489`) + the designated Surface family: FnSpecs over real raft `quorum` functions with MeetsSpec corollaries, negative twins, Terminates, TotalReadout — the working function-scale template | `Challenge.lean:50-264`; L-13 |
| **Adequacy / exit** | plain + strong + initial-heap + invariance adequacy; Iris-free exit doors to `execStmt`/`stepFnIter` first-order statements (`GoSpec` = triple ∧ progress, frame preservation in the statement) | `Adequacy.lean:83/141/215/280`; `SurfaceExit.lean:96,145`; `Surface.lean:210,384` |
| **Per-construct rules** | seq/blocks/if/while(+Löb invariants, break leg)/assign spine/generic strict-op spine/static calls (small arities)/interface dispatch (arity-2)/func-value (cap-1 nullary void)/defer-panic-recover (rich)/StmtOp spine/make/map-range (key-only)/map lookup comma-ok/slice index-len-store/sort (per-site premise)/fork (LangC/D) | `Laws/*` — scout coverage table, 11 files, 6,120 lines |
| **Case-split** | boolean/if laws + the two-leg while-invariant; tier-1 kit (Crossing, landing) for the correspondence-side work | `Laws/Eval.lean:383-427`; L-4 |
| **Automation** | `go_walk` (603 lines): deterministic walks; registered-law driven | `Tactics/GoWalk.lean:31-49` |
| **Non-vacuity discipline** | live at this tier — witnesses per law, two tombstones for vacuous-by-domain laws, a kernel-checked load-bearing-pin demo | `Laws/Range.lean:328,356`; `Laws/Call.lean:898`; `Ghost.lean:53-55` |

### 5.2 The choice-tape thread (how nondeterminism crosses the tiers)

Tape (`Choices`) lives ONLY at tier 1 (`stepFn`); tier 2 is
tape-free — latitude is demonic rule multiplicity (`mapIterNext`'s
∀-idx, append-capacity/select ∃-premises), so every WP proof is
∀-schedule by construction and the ∀-ch quantifier of the harness
sentences is discharged at the adequacy readout
(`execStmt_sound_normal` erases ch). The ∃-side (CompletionWitness,
reflection certificates) is discharged executable-side, where the
tape is concrete — no relational route needed. The one soundness
asymmetry: `Steps`-reachable ⊇ `stepFnIter`-reachable is proved;
the converse (stream stitching) is NOT (`MachineSound.lean:593-598`)
— fine for the ∀-facts the sentences need, named below as the
optional G-STITCH.

### 5.3 MISSING — the named units (each: obligation shape + what LAND feeds it)

| unit | the gap | obligation shape | consumes from LAND | [AGENT] size signal |
|---|---|---|---|---|
| **G-REPR** | assertion layer: heap is base-address-only whole-cell (`HeapBridge.lean:26-48` silently — soundly — drops field/index keys); one `↦` owns an entire nested struct; no `own_slice`/`own_map`/`own_struct`, no per-field framing. THE blocking design gap for raft's deep struct heaps | representation predicates over `HeapCell` + get/set access lemmas + ∃-address genericity; LINEAGE: Perennial `new/golang/defn` typed model + RefinedC type-assignment | readers (L-5) as pure projections; `_ren` spine until subsumed | largest single design unit; measured probe first |
| **G-BIND** | no `wp_bind`: bare CEK Language, hand-built continuation-frame spine, per-arity frame-entry laws | fill/step commutation over `Cont` (an EctxLanguage-style mixin or a direct bind lemma family); gate instance at a real lowered call site | **the plug family (L-1) — `plugK` is the fill, `stepFn_plug`/`callSpan_plug` the commutation content**; W1 probe finding as the design constraint | 1–1.5 sessions against the W2 measured anchor (2,948 lines/session, probe-first) |
| **G-CALLS** | call laws hardcoded per (arity, result-count); alloc cores fixed 1–4 cells ("list-indexed generalization stays owed", `Lifting.lean:246,309`); func-value-field dispatch (raft's `r.step`) has no composed law; `(T, error)` returns unservable | n-ary `wp_call_enter`/`wp_frame_return` over list-indexed allocation; a func-value-field read∘enter composition law | G-BIND reduces the per-geometry surface; the cancelled CallSpecV's *site census* (w3-m park record) prices it | 1–2 sessions |
| **G-MAPITER** | `wp_map_iter_inv` key-only, mutation-free, no order/Perm conclusion (`Laws/Range.lean:190-193,403-405`) | key+value, stop-admitting, mutation-tolerant range-over-map invariant law with demonic order and a Perm-of-draws readback | **MapPerm/MapLoops (L-3)** — the Perm algebra and width facts are the soundness content; discharges the ∀-draw quantifier at tier 3; also the mapPickLoop_perm witness lands here (§1.4) | 1 session |
| **G-EXIT** | no `runProgramM` exit theorem: adequacy stops at `execStmt`; the designated sentences are `runProgramM`-shaped | `WP` at the entry config + setup boundary ⇒ AgreementT1-shaped readout (globals seed + `$pkginit` + entry wiring) | **RunGlue (L-2)** + **InitSpec (L-8)** are its two halves | 0.5–1 session |
| **G-STMTS** | TotalT1/NeverFaults exist only as prose; designation never executed; the raft statements extend the Surface FuncSpec idiom (L-13) | `Prop` drafts + the NeverFaults-from-Total corollary via `runProgramM_classify_of_total`; then the [USER] designation act + judge | RunGlue (the corollary engine) | 0.5 session + [USER] ceremony |
| **G-INV** | the driver-loop invariant as an Iris-tier predicate; the [USER]-gated W2.5 amendment (concrete-log↔NH pairing incl. the AbsLog data-axis reader, freshLog vote-square, quiescence, Star/certified transport — the v3 §D-A designs, re-shaped for tier 3) | pure clause inventory (L-6) ⌜–⌝-embedded + G-REPR heap parts; **the design gate is the [USER]'s — non-negotiable, the F-1 lesson** | Invariant contract (L-6), readers (L-5), ghost-acks (L-7) | ~2 sessions + user gate (v3 anchor) |
| **G-AUTO** | `go_walk` stops at invariant rules, nondet branches, real store obligations, resource splits (`Tactics/GoWalk.lean:51-64`); u64 obligations are hand-`omega`; the largest shipped Iris walk is ~2 functions (`GoldenQuorumWP.lean`, 1,512 lines) vs raft 3–4 orders larger | wp_apply-class law application + normalization automation + a measured throughput probe BEFORE the first cluster charter (the middle-path rule: measured fragility, not hypothetical) | kit (L-4) patterns inform the case-split automation | probe first; size unknown, honestly |
| **G-SORT** | `wp_sort_slice`'s effect premise re-proved per call site (`Laws/StmtOps.lean:672-681`) | symbolic sort law packaging the existing permutation/mergeSort infrastructure (`Laws/Values.lean:245-405`) + `sortedLT_eq_of_perm` | MapPerm (L-3) | days |
| **G-STITCH** *(optional)* | the iterated exec-realization converse (stream stitching) — needed only if ∃-shaped claims ever route through the relation | per-step `step_complete` chained with a stream-concatenation lemma | tier-2 only | days; defer until demanded |
| **G-CONC** *(post-T1)* | channels/select/sync laws; StepM pairing inexpressible in iris-lean's thread-pool Language (proven obstruction, `Surface.lean:591-601`) | the channel-logic resume (P-1) under its named conditions | LangC/LangD seam (L-12) | out of T1 scope |

**Headline: how far is the stack from raft-ready?** Tier 2: ready
(no construct gaps; one optional lemma). Tier 3: the architecture is
real and proven at function scale on real raft library code (the
quorum family), but the raft HARNESS is blocked behind five
structural units — **G-REPR (the big one), G-BIND, G-CALLS,
G-MAPITER, G-EXIT** — plus the statement/invariant acts (G-STMTS,
G-INV) and a throughput probe (G-AUTO) before any cluster spends.
[AGENT] honest read: that is roughly 6–10 worker-sessions of
structural buildout before leaf-spec work begins, against v3's
measured session anchors — the follow-on plan document prices it
properly; the corpus (§7) is how the units get exercised without
betting the raft walk on them.

---

## 6. NUMBERS (derivation-anchored)

**The wave (w1-prover vs main):** 56 files, +39,462/−10
(`git diff --stat main...HEAD`). Disposition:

| verdict | Lean lines | share of wave Lean | derivation |
|---|---|---|---|
| KILL (never lands) | ≈28,440 | ≈78% | K-1a 483 + K-1b 8,569−100 + K-1c 925 + K-1d 18,270+296 (per-file `wc -l` at the tip, §2) |
| LAND (Lean) | ≈7,700 | ≈22% | L-1 2,883 + L-2 494 + L-3 752+90+847+~100 salvage + L-4 376 + L-5 993+81 + L-6 ~625 + L-7 160 + L-8 153 + L-10 ~130 pruned pins + root-import delta |
| LAND (docs) | ≈3,210 | — | five logs 2,415 + three notes 794 + registry +12 |

**Main's delta at landing:** proofs tree 279,724 → ≈287,160 Lean
lines (+7,700 −260 main-side kills; ≈+2.7%). Docs +≈5,260 (the
wave's 3,210 + symbolic-domain 901 + layerc + ARCHIVE/registry
sections). Files: +15 Lean modules, −2 main-side, −0 under
`GoLean/`/`scripts/`/`baselines/` (trust surface untouched —
verified `git diff --stat main..w1-prover` on those trees = Audit
imports only).

**Build implications (measured anchors):** the wave tip's full build
was 545 jobs, warm wall 63–65 s, peak RSS 7.0 GB (w3-prover-log:843);
the landing DROPS the elaboration tail — the six member modules
measured 125–159 s EACH (w3-prover-log:937,974), the 15.9k generated
`BfLit`/`CBfLit` literals, and the 38 s W2Gate instance
(w2-prover-log:161). The landed heavy module is `PlugStep`
(`maxHeartbeats 6400000`, one ~200-arm walk) — already inside the
measured W2 session cost, elaborates once. Net: post-landing main
builds STRICTLY lighter than the wave tip and only ≈15 modules
heavier than today's main; the aggregate-RSS OOM class
(operational-lessons §2: 6–8 concurrent window-kernel modules
breached 96 G) loses its worst members. The judge's fresh-clone cold
build (122.8 G peak incident) also benefits from the −28.4k lines.

**Counts per list:** LAND 15 Lean modules + 2 modified-file deltas +
9 docs; KILL 17 Lean modules + 1 tool + 2 main-side modules + pin
prunes; PARK 3 lanes (one HIGH-risk), 1 doc-landing lane closure,
8 worktree prunes.

---

## 7. THE PATTERN INVENTORY AND CORPUS-SEED ASSESSMENT

([USER] aim: a target corpus of small programs covering ALL the
patterns raft needs — "enough richness that cheating is hard, but
tiny enough to motivate success" — to exercise the Iris layer.
Inventory + coverage matrix ONLY; corpus design is the follow-on
unit.)

### 7.1 The pattern classes raft exercises

Derived from the census (fragment reachability + choice sites), the
W3 prover logs' machine findings (measured windows, crossing maps,
the Clone/symdiff probes), and the harness anatomy. Fifteen classes:

| # | pattern | raft site (evidence) |
|---|---|---|
| PC-1 | map-range draw with demonic order, key+value, Perm-stable readback | driver pick loop (twin-chdriver.go:60); tally counting; Progress iteration (census U4/U5) |
| PC-2 | mutex Lock/defer Unlock walks, both return geometries (plain return; defer-tail with result) | `MustSync`, `Term`, storage walks (w3 log: term trichotomy 433/840/1040-step windows; mustCheck 695/329) |
| PC-3 | symbolic data-branch crossings: Int-beq bridges, trichotomies, slice validation | maybeTerm/Term error trichotomy; the kit's three archived discharges |
| PC-4 | interface dispatch at pinned fields (Logger, Storage, quorum ifaces) | raft.go's iface calls; census cluster F |
| PC-5 | func-value call sites incl. struct-field dispatch | `r.step` (raft.go:1284); confchange closures (Clone probe: closures drain via `callValArgsK`) |
| PC-6 | deep-struct clone/copy chains | `Config.Clone`/`Restore` (w3-m park: 326-step probe, capacity-hint dropped by the frontend) |
| PC-7 | loops with multiset/Perm invariants + sort readback | `JointConfig.IDs` (the archived (M) member); `VoterNodes` sort; `slices.Sort` census (unowned, F-4) |
| PC-8 | append-capacity latitude (tape-demonic growth) | entry append paths; `stmtOpApply`'s ∃-ch |
| PC-9 | message-multiset harvest/drain loops | `msgs`/`msgsAfterAppend` drains; Ready/acceptReady/Advance (B-cluster park records) |
| PC-10 | error-global trichotomies / `(T, error)` returns | ErrCompacted/ErrUnavailable (`raftLog_zeroTerm_*` archived trio) |
| PC-11 | u64 wraparound arithmetic density | log index arithmetic (the `i − offset < 2^63` family bounds; wrap-per-op rule, w3 log) |
| PC-12 | comma-ok idioms (map lookup; type assert) | symdiff probe (`.mapLookup` comma-ok); AckedIndex |
| PC-13 | nested field-chain access (`r.raftLog.storage…`) | everywhere; the G-REPR stress case |
| PC-14 | init chains: globals seed + `$pkginit` + constructor cascades | newRaft/NewRawNode (init stage B, archived Wave A members) |
| PC-15 | defer/panic/recover through real frames | assertion branches (census U3) |

### 7.2 The seed pool — what already exercises the Iris tier

Existing Iris-track subjects (verified `WP (` consumers): the golden
inc pin, GoldenRecover, the three quorum pilots (+`committedIndex
AllConfigs` ∀-family), GoldenSliceWP (sort), GooseParity
{Nil,Vars,New,Block}WP + Kit, Fib, AutomationTargets. The 26-program
gallery (67 files under `Examples/`) is stepFn-track — ZERO `WP (`
in its flagships (SliceQueue 8,343 lines, SliceStack, MatMul,
Kadane… — verified by the tier scout) — so it seeds PATTERNS and
lowered programs, not Iris proofs; re-speccing a gallery program at
tier 3 is itself corpus exercise.

### 7.3 The coverage matrix

| pattern | Iris-tier seed today | tier-3 rule support (§5) | corpus need |
|---|---|---|---|
| PC-1 map-range demonic | `wp_map_iter_*` witnesses (key-only micro) | partial (G-MAPITER) | **NEW: 1–2** (key+value walk w/ Perm readback; a mutating-body variant) — Histogram/WordFreq are stepFn-track seeds to re-spec |
| PC-2 lock/defer geometries | GoldenRecover (recover only) | defer/panic rich; RD-geometry untested | **NEW: 1–2** (lock+defer read; defer-tail with result) |
| PC-3 branch crossings | quorum pilots (mild) | if/while laws fine; automation-bound | **NEW: 1** (trichotomy function); BinSearch re-spec optional |
| PC-4 interface dispatch | quorumAckedIndex (method, arity-2) | `wp_call_dynamic_enter₂` only | **NEW: 1** (n-ary iface method) after G-CALLS |
| PC-5 func-value fields | — | cap-1 nullary void only | **NEW: 1–2** (the `r.step` shape in miniature) — G-CALLS gate |
| PC-6 deep clone | — | blocked on G-REPR | **NEW: 1** (small proto-clone) — the G-REPR gate instance |
| PC-7 Perm/sort loops | GoldenSliceWP (per-site sort) | G-MAPITER/G-SORT | **NEW: 1** (mini-IDs: build map → collect → sort) — doubles as the mapPickLoop_perm witness site (§1.4) |
| PC-8 append capacity | — (SliceStack/Queue are stepFn-track) | `stmtOpApply` covered relationally | **NEW: 1** or SliceStack re-spec |
| PC-9 harvest drains | — | needs PC-1/PC-2 pieces | **NEW: 1** (produce-then-drain queue) |
| PC-10 error returns | — | blocked on G-CALLS (`(T,error)`) | **NEW: 1** |
| PC-11 u64 density | quorum pilots (real, `.uint64`) | works; throughput-bound (G-AUTO) | covered; grow via others |
| PC-12 comma-ok | quorumAckedIndexFuncSpec2; `wp_map_lookup` | covered | covered |
| PC-13 nested fields | golden pin (shallow) | G-REPR | exercised via PC-6 |
| PC-14 init chains | — | G-EXIT territory | **NEW: 1** (globals+pkginit mini) — doubles as G-EXIT's gate instance |
| PC-15 panic/recover | GoldenRecover + `Laws/Unwind` witnesses | rich | covered |

**Assessment:** the seed pool genuinely covers PC-11/12/15 and
partially PC-1/2/3/4/7/13; wholly uncovered are PC-5/6/8/9/10/14 —
exactly the classes sitting behind G-REPR/G-CALLS/G-MAPITER/G-EXIT,
which is the right shape: **each structural unit of §5.3 should land
with its corpus program as the gate instance** (the W2 gate
discipline, re-aimed). [AGENT] estimate: **≈10–14 new small
programs** (rows above sum 10–14), plus 2–3 gallery re-specs
(Histogram, SliceStack, BinSearch) as cheap width — with the
differential-first rule applying to every new program (guardrail
corpus cases before Iris proofs, per charter). Counted, this is the
corpus-design unit's input, not its output.

---

## 8. OPEN [USER] CALLS AT SIGN-OFF (collected)

1. **The witness posture** (§1.4): scaffold-label
   `mapPickLoop_perm` + judgment-free mini-witnesses (recommended)
   vs retaining ~1,571 lines of live CallSpec witness chain.
2. **Invariant.lean lands vs archives** (L-6 [AGENT] judgment
   flagged): recommended LAND (G-INV's base inventory; Hygiene
   consumes plug).
3. **The W2Gate gap** (K-1c): accept losing the end-to-end
   composition demo until G-BIND's gate instance (recommended) or
   direct otherwise.
4. **LangC/LangD**: keep-in-place with registry note (recommended)
   vs park.
5. **The designation acts** (L-13/G-STMTS): scope of the gallery-row
   reclassification; TotalT1-as-THE-sentence posture (the recorded
   end-state doctrine) — confirm at drafting, designate at landing.
6. **Ref deletions** for the merged arc branches (P-5) — housekeeping,
   [USER] pleasure.
7. **The G-INV design gate** — reaffirmed as a [USER] gate (the F-1
   lesson); nothing in this plan pre-empts it.
8. **Disposition of the design-pass deliverables** (findings,
   v3-DRAFT superseded-in-architecture, this plan) at the ceremony.

---

*[AGENT] provenance: all verdicts, size signals, and
recommendations above are the triage planner's, from primary
sources; [USER] provenance is marked where a decision is recorded
from the campaign log or the coordinator's mid-pass update. No
execution has occurred: no file outside the design-pass worktree was
modified.*
