# W3 log (2026-08-27) — one writer: the w3 Wave-3.0 worker (same lane, W2's successor); continued by the U3.0d/U3.1-F worker (same lane, Wave-3.0's successor)

**Charter**: the campaign worktree's `docs/2026-08-27_w3-charter.md`,
Wave 3.0 (units U3.0a/U3.0b/U3.0c — the interface wave). Contract:
`docs/2026-08-27_w25-invariant-design.md` (ADOPTED by [AGENT]
adjudication; the adjudication itself is a mandatory [USER] review
item at the landing ceremony — restated here so the flag survives).
Branch `w1-prover` @ 849b3707 (inherited; ONE WRITER — W2's worker
retired). Conventions unchanged: capped builds only, box-wide lock
for full builds, zero sorry/native_decide/new axioms, [AGENT]
provenance, derivation-anchored numbers, no subject-run counts in
exported statements.

**QUANTIFIER-AUDIT LINE (the charter's opening requirement):** Wave
3.0 is the INTERFACE WAVE — it advances NO end-theorem quantifier by
itself and says so per unit:
- U3.0a (ghost-acks): interface only — the acks carrier + the
  `certified` instantiation C4's ack clause and W3.2b's
  Match-evidence unit consume. No quantifier advanced.
- U3.0b (readers): vocabulary only — the C3 lens readers with their
  `_ren` congruences; consumed by every clause that mentions the
  checker state. No quantifier advanced.
- U3.0c (the invariant module): the DEFINITION of `I` — the predicate
  whose preservation (W3 body specs), establishment (W3.2f), and loop
  instance (W4) later discharge ∀-states/∀-iterations. Defining `I`
  advances no quantifier; the definition is the contract those rules
  will discharge against.

## Successor re-verification (W2's top claims, re-checked before any work)

All checks run 2026-08-27 against the inherited worktree.

- **Tip + cleanliness**: `git log` head = `849b3707` ("W2 gate
  record… branch-complete"), `git status` clean. CONFIRMED.
- **Gate log on record**: `artifacts/w2/ci-gate.log` tail =
  `RESULT: PASS`, `GATE_EXIT=0`. CONFIRMED.
- **Hatch grep**: `grep -rn "sorry\|native_decide" proofs/GoLeanProofs/`
  → doc-comment mentions only (6 docstring hits, 0 live). CONFIRMED.
- **The two retained witnesses are in-build**: `NativeS1Witness` /
  `NativeS23Witness` imported by `proofs/GoLeanProofs.lean` (lines
  63/65) — the standing non-vacuity gauges this wave must keep green.
  CONFIRMED (build-enforced).
- **Box-wide build lock**: owner file reads RELEASED (W2's exit,
  09:23Z); zero lake/lean batch processes on the box. CONFIRMED.
- **W2 gate artifacts spot-check**: `w2_gate` present at
  `Specs/RaftPilot/W2Gate.lean:282` with the composition exactly as
  logged (CallSpec + FrameSim + callSpan_plug + absRaftNode_frameSim);
  `Audit/W2.lean` present and imported. CONFIRMED by reading.

Verdict: W2's record stands as claimed; work begins from 849b3707.

## Judgment calls and checkpoints

(one-line [AGENT] entries appended per decision; checkpoint block
after each unit)

- [AGENT] Sandbox note: /tmp is write-only in this session's sandbox
  (`nono why`: read denied); build logs go to repo-local
  `artifacts/w3/` (the predecessors' convention anyway). No
  workaround of the sandbox attempted.
- [AGENT] U3.0a shape: acks entries are `(term, ackedIndex)` pairs,
  per-acker (`acks : Nat → List (Nat × Nat)`, the exact `votes`
  mirror); `ackCertified voters g tm idx` = ∃ quorum, each member has
  an ack `(tm, k)` with `idx ≤ k` (prefix-acknowledgement reading —
  matches the note's "recorded at ≥ the index"). The EStep/HStep
  wiring is TRANSPARENCY + the named instantiation, not new
  constructors: `EStep` provably never writes acks
  (`EStep_acks_eq`); `HStep`'s abstract `certified` parameter keeps
  its shape and `ackCertified` is documented as its intended
  instantiation (performed at W3.2b, not here). Extending EStep with
  an AppResp constructor was NOT done — the election fragment has no
  AppResp step, and inventing one here would reshape the S1 dialect
  the discharge layer is proved against.

## U3.0a — THE GHOST-ACKS EXTENSION: LANDED

- Files: `Specs/Raft/NativeObligations.lean` (Ghost + `acks` field;
  `ackCertified` + `ackCertified_mono` + `ackCertified_le`),
  `Specs/Raft/NativeEtcdDischarge.lean` (`pushAck` + self/other/
  votes/victories frame lemmas; `pushVote_acks`/`pushVictory_acks`;
  `mem_acks_pushAck`; `EStep_acks_eq`; `ackCertified_estep`),
  `Specs/Raft/NativeS1Witness.lean` (wG0 acks field; WITNESS 4
  `witness_ackCertified` — ackCertified inhabited via two pushAcks at
  the twin's 2-of-3 shape; WITNESS 5 `witness_acks_transparent`).
- Quantifier line: interface only; advances no quantifier (stated in
  the Ghost docstring).
- **The two retained interface witnesses re-run and GREEN** after the
  extension (NativeS1Witness / NativeS23Witness rebuilt in the same
  target set; no witness claim changed — the S1 witness gained two
  NEW theorems, its existing four steps + three witnesses untouched).
- Build: `lake build GoLeanProofs.Specs.Raft.NativeCheckerBridge
  …NativeS1Witness …NativeS23Witness` capped 48G/4 threads →
  EXIT=0, 28 jobs (artifacts/w3/u30a-build.log); `Audit.CheckerBridge`
  pins EXIT=0 (u30a-audit.log). Wall: ~1 min class (warm imports;
  the 28-job log's own duration — no single module above seconds).
- No Audit pin changes; no trust-surface files touched.

- [AGENT] U3.0b scope call: a FIFTH reader added beyond the
  charter's four — `absNetMeta` (per net message, the entries'
  `(Type, Data)` metadata). Reason: C4's population clause
  ("all entries EntryNormal") and payload clause's data axis are
  UNSTATABLE over `absMessage`'s `(Index, Term)` entry projection;
  without this reader U3.0c would need a joint parameter for a
  cheaply-definable lens — the wrong side of the fail-closed rule.
  Charter estimate corrected, not silently exceeded.
- [AGENT] U3.0b map-order honesty: Go map iteration order is
  LATITUDE; `mapRead` exposes the machine's `mapData` store order
  only because an assoc list must have one. Stated in the module
  docstring; the invariant module consumes the maps through LOOKUP
  vocabulary only, never order.
- [AGENT] U3.0b lens choice: the map lens (`mapRead`) is NEW (maps
  were unprojected before); kept file-local per the promotion
  ledger's ≥2 rule — promotion to `Lens.lean` when a second consumer
  bites. `locField`/`ptrField` (deref+field with TypeId check) are
  likewise local; they generalize `fieldRead` off `.base`-only
  addresses.

## U3.0b — THE READER EXTENSION: LANDED

- File: `Specs/Raft/AbsTwinCheckerRead.lean` (new, beside
  AbsTwinRead; registered in `proofs/GoLeanProofs.lean`). NO change
  to AbsTwinV0 or any of its consumers (AbsTwinRead untouched).
- Readers (each total, fail-closed, TypeId-checked): `absLeaderOf`
  (term ↦ claimer assoc), `absByIndex` (index ↦ (term, data,
  firstNode) via the embedded `main.slot` decode), `absNodeCursors`
  (per-node applied/lastTrm), `absNodeGot` (per-node data ↦ flag),
  `absNetMeta` (per-message entry (Type, Data) — the [AGENT] fifth).
- `_ren` congruences in the RenCongr/L4 style, composed from the
  lens laws (sliceRead_ren + new mapPairs_ren/mapRead_ren +
  locField_ren/ptrField_ren + pure-decoder invariances):
  `absLeaderOf_ren`, `absByIndex_ren`, `absNodeCursors_ren`,
  `absNodeGot_ren`, `absNetMeta_ren` (+ element-level lemmas).
- Definedness under C1 well-shapedness: generic `MapFieldShaped`/
  `SliceFieldShaped` + `mapField_defined`/`sliceField_defined`
  (with the slice length equation), instantiated per reader:
  `absLeaderOf_defined`, `absByIndex_defined`,
  `absNodeCursors_defined`, `absNodeGot_defined`,
  `absNetMeta_defined`. Non-vacuity of the shape premises: the
  in-file `wTwinState` 4-cell state (wTwin_leaderOf/wTwin_cursors
  compute; wTwin_leaderOfShaped discharges LeaderOfShaped).
- Build: file elaboration EXIT=0 with zero warnings in the new file
  (artifacts/w3/u30b-check.log); `lake build …AbsTwinCheckerRead`
  EXIT=0, 43 jobs, module 0.5 s (u30b-build.log).
- Quantifier line: vocabulary only; advances no quantifier (module
  docstring).

- [AGENT] U3.0c structural call — THE HOISTED CARRIER PACK: the
  note's `CheckerCorr ⊆ Pair`/`NetCorr ⊆ Pair` and the phase split
  all speak about the same ∃-witnesses (the ghost-completed net, the
  two event histories); a literal per-clause ∃ would let each clause
  pick a DIFFERENT carrier. `AbsCarrier` (N, evsS1, evsA) is one
  pack shared by Pair/CheckerCorr/NetCorr/phase inside `I.pair` —
  the one departure from the note's surface syntax, semantic intent
  preserved (arguably repaired).
- [AGENT] U3.0c trace strengthening — `ClaimTraceTo` (endpoint-named
  observation trace): the landed `ClaimTrace` truncates anywhere,
  which the leaf tolerates but PRESERVATION cannot (extending the
  trace at a new claim needs the frontier tied to the current
  carrier). `ClaimTraceTo` adds the endpoint; `toClaimTrace` forgets
  it (sanity lemma), so every landed consumer is served. C3(a) is
  stated at the strengthened form.
- [AGENT] U3.0c faithfulness inventory (clause → note): Base=C1
  (statics/logger/lift-definedness incl. the new readers' via
  Base.leaderOfRead…netMetaRead); Pair=C2 (∃-placement `NodePlaced`
  with FrameSim placement data + carrier-side deep-reader agreement
  `s1Agrees` on state/term/vote/lead — COMMIT OUTSIDE, per the
  stutter-provability flag; `shellSync` on state/term; SNet Reach
  carrier + Seed); CheckerCorr=C3 (a=trace, b=leaderOf/claims
  equations, c=byIndex/cursors/got, e=violations equation — the
  "+0" reading: every non-model guard silence is the equation's
  preservation obligation, named per the T1-V census; d lives in
  ElectedAt.appliedLogs); NetCorr=C4 population/entryTypes/hgen
  (phase-shared) + ElectedNet payload/ack (Elected-scoped — in
  Electing they are vacuous BY POPULATION restriction, not stub);
  Hygiene=C5 context half (mapIterFree + recoverThroughWrappers =
  none); Stream=C5 stream half as the state-level suffix clause
  (ch <:+ ch₀ — the per-round suffix accounting; span-level
  ∀ch/draw discipline lives in the specs, not the state); phase
  split per the note (Electing: victories=[], evsS1=[], evsA=[],
  net vote-family {Vote,VoteResp}; Elected: ghost victory on record
  + H-carrier HistInv/Star HStep with `certified :=
  ackCertified voters ghost tm` VERBATIM + log/commit bridges +
  deep commit/applied ties + C3(d) + ElectedNet).
- [AGENT] U3.0c additions beyond the note's letter (each cheap,
  recorded): Pair.count/Pair.ids (concrete node list ↔ voter set —
  the configuration-shape facts quorum instantiation needs);
  NetCorr.metaLen (positional alignment of the metadata reader with
  tv.net, carried as a clause instead of a lemma against
  absTwinRead's private walk); ElectedAt.deepCommit (the deep
  reader's commit/applied axes tied to the H-carrier — the
  "per-carrier field selection" the note's C2 describes, read
  directly on σ, coinciding with the carrier read by
  absRaftNode_frameSim).
- [AGENT] U3.0c population reading: general population lists the
  note's five types incl. Prop(local); Electing restricts to
  {Vote, VoteResp} (the note's "vote-family only", read strictly).
  The harvest folds only rd.Messages into the net, so MsgProp
  should never appear — W3.1's emission census may tighten the
  general clause to the four wire types; recorded, not silently
  tightened.

## U3.0c — THE INVARIANT MODULE: LANDED

- File: `Specs/RaftPilot/Invariant.lean` (new; registered in
  `proofs/GoLeanProofs.lean`), namespace `GoLean.RaftSeam.Inv`.
- Key definitions: `I` (Base ∧ Pair(+CheckerCorr+NetCorr) ∧ Hygiene
  ∧ Stream ∧ (Electing ∨ ∃ ldr tm H₀ NH, ElectedAt)); `AbsCarrier`;
  `Base`; `s1Agrees`/`NodePlaced`/`shellSync`/`Pair`;
  `ClaimTraceTo`; `lookupI`/`LeaderOfCorr`/`ByIndexCorr`/`GotCorr`/
  `CheckerCorr`; `NetCorr`; `Electing`; `hlogBridge`/`ElectedNet`/
  `ElectedAt`; `Hygiene`; constants msgProp/msgApp/msgAppResp/
  msgVote/msgVoteResp/entryNormalTy (raftpb-cited); `asNat` (the
  precise Int↔Nat bridge — no `Int.toNat` negative-collapse).
- Sanity lemmas (definitions-plus-cheap-lemmas charter): `I.twinRead`
  (definedness projection), `I.abs_oneLeaderPerTerm` (the S1 chain
  plugs into the carrier — etcd_discharges + native chain),
  `ClaimTraceTo.toClaimTrace`/`ClaimTraceTo.reach`,
  `CheckerCorr.claimTrace`, `claims_zero_of_electing`,
  `violations_zero_of_electing` (the fold equations have
  computational teeth), `ElectedAt.victory_recorded`,
  `ElectedAt.histInv_end` (histInv_reachable surfaced).
- NO preservation, NO establishment (later waves', by charter). NO
  `True` stubs (grep clean); every not-yet-supplied piece is a NAMED
  parameter (below).
- Hatch grep over all W3-touched files: 0 sorry/native_decide/
  partial.
- Builds: module elaboration EXIT=0, zero warnings
  (artifacts/w3/u30c-check.log); target build EXIT=0, 59 jobs,
  module 0.8 s (u30c-build.log); **wave-boundary FULL proofs build
  (lock held + released): EXIT=0, 537 jobs, wall 5.09 s (warm tree —
  only the roots rebuilt), peak RSS 2.2 GB**
  (u30c-full-build.log/.time). No differential owed (proofs/docs
  only); a full scripts/ci gate is not required at this wave
  boundary per the wave charter.

## THE JOINTS LEFT FOR LATER WAVES (the named-parameter ledger)

1. `dataEnc : List Int → Nat → Prop` — the data-encoding relation
   (concrete command bytes ↔ abstract data ids; the arc4d encGS
   seam). `I` is parameterized by it; W3.2d (checker reshape)
   supplies the concrete instance.
2. `tl : Loc` (the twin location) and `N₀ : SNet` (the abstract
   seed) — `I`'s parameters; W3.2f (init stage B / establishment)
   supplies the concrete values and proves `I` at the loop head
   (the base case). `I` has NO inhabitation witness until then —
   charter-sanctioned, restated in the module docstring.
3. `certified`'s premises: the Elected carrier uses
   `ackCertified voters ghost tm` verbatim (U3.0a); W3.2b discharges
   `leaderCommitOk` from the ghost acks at the commit-advance.
4. `H₀`/the phase transition: W3.2a's winning-MsgVoteResp spec
   establishes ElectedAt (H₀ from the noop-first-propose; (ldr,tm)
   fixed by the population clause, per the note).
5. Guard silences: CheckerCorr.violations equates the concrete
   counter with the MODEL folds' sum; each non-model guard's
   silence (S3 anomaly, harness guards at twin-lib 236/245/254/262/
   455/472/489) is a W3 handler-spec conclusion per the T1-V census
   — the equation is their consumption site.
6. NOT COVERED by `I`, recorded: twin.committed (the harness's
   non-empty-apply counter) has no correspondence clause — the note
   names none and no consumer exists yet; S4/complete() is an
   END-of-run check, outside the loop invariant by design (W4's
   post-loop obligation, not `I`'s).

## WAVE 3.0 CHECKPOINT (branch-complete for the wave)

- Units: U3.0a LANDED (b3a21913), U3.0b LANDED (040b7164),
  U3.0c LANDED (this commit). Sequential, one writer, one commit
  per unit.
- The two retained interface witnesses: GREEN throughout (re-run at
  U3.0a; in every subsequent full-target build).
- Nothing trust-adjacent touched: no Audit/*, no scripts/*, no
  GoCore, no baselines; `proofs/GoLeanProofs.lean` gained two
  imports (proof-layer aggregation, not trusted closure).
- FOR THE LANDING AUDIT (restated): the W2.5 [AGENT] adjudication
  that adopted the invariant design is a mandatory [USER] review
  item; this wave BUILT AGAINST that adopted contract.
- Wave 3.1 handler-census inputs discovered here: (a) MsgProp
  never enters the net via harvest (rd.Messages only) — the
  population clause can likely tighten to four wire types; (b) the
  emission-census conclusions each handler owes are exactly
  NetCorr's four clauses at the U3.0b/U3.0c vocabulary (the
  entryTypes clause needs emitted-entry typing, i.e. appendEntry/
  bcastAppend specs must conclude EntryNormal typing through
  absNetMeta); (c) shell-sync (state/term) means every harvest
  handler spec owes the shell-update ↔ deep-reader agreement at
  its Ready processing; (d) the cursors equation keys the s23 fold
  at node id = list index + 1 — the apply-loop spec should conclude
  exactly that keying.

---

# W3 continuation (2026-08-27) — units U3.0d + U3.1-F (one writer; Wave-3.0's successor on the same lane)

Charter: `docs/2026-08-27_w3-charter.md` INCLUDING AMENDMENT 1
(census-derived, binding) + the coordinator's unit brief. Census
instrument: the campaign worktree's
`docs/2026-08-27_w31-reachability-census.md` ([AGENT] instrument —
claims built on are re-verified against the wire below).

**QUANTIFIER-AUDIT LINE:** U3.0d is invariant-definition work
(interface: advances no quantifier — the folded clauses are the
contract later preservation/establishment rules discharge). U3.1-F
builds CallSpecs = the RULES that discharge ∀-state at the log/util
call sites of clusters C/D/E, plus the result-bearing judgment form
(rule machinery). No end-theorem quantifier closes in either unit,
and each spec's docstring says which ∀ it serves.

## Successor re-verification (Wave 3.0's top claims, re-checked)

- Tip + cleanliness: `git log` head = `562eb988` (U3.0c invariant
  module commit), `git status` clean. CONFIRMED.
- Full-build claim: warm full proofs build re-run at start of this
  session (as the U3.0d wave-boundary build below) — 537 jobs,
  EXIT=0. CONFIRMED (same job count as the U3.0c record).
- Invariant module zero-True-stubs: grep over
  `Specs/RaftPilot/Invariant.lean` for `True` stubs → none; the
  joint ledger's named parameters (`dataEnc`, `tl`/`N₀`, `H₀`,
  guard silences) present as parameters, as recorded. CONFIRMED.
- U3.0b readers present incl. the [AGENT] fifth (`absNetMeta`) with
  `_ren` + definedness; wTwin non-vacuity state in-file. CONFIRMED
  by reading `Specs/Raft/AbsTwinCheckerRead.lean`.
- Build lock: owner file read RELEASED (Wave 3.0's exit); only idle
  LSP workers on the box (a prior arc4d session + an unrelated
  project) — same inventory as the predecessor's note. CONFIRMED.

## Judgment calls — U3.0d

- [AGENT] Census re-verification performed against the wire/subject
  before building on it: (a) §3.1's four-type net alphabet re-derived
  from the harvest fold (twin-lib.go:283-286 folds `rd.Messages`
  only) + `stepFollower:1748` unreachability (nodes 2/3 never
  proposed to; node 1 never a follower — predecessor's discovery (a)
  agrees); (b) §2.4's Progress bounds re-read at raft.go:815-823
  (reset: follower Match=0, Next=lastIndex+1; self Match=lastIndex)
  and log.go:387-413 (term's TWO error arms — ErrCompacted at
  i+1 < firstIndex, **ErrUnavailable at i > lastIndex**); (c) the
  tracker shapes re-read from the pinned wire's typeDefs
  (tracker.ProgressTracker/Progress/Inflights fields, probe
  artifacts/w3/ProbeTypes.lean output).
- [AGENT] TERM-BOUND formulation (Amendment 1 left it to the
  worker): `tm` HOISTED into `AbsCarrier` (the same one-pack move as
  U3.0c's carrier hoist; the Elected phase term is pinned to `A.tm`
  in `I.pair`, so the bound's witness and the phase term can never
  diverge). Node half in `Pair` (`tmPos : 1 ≤ A.tm`;
  `terms : ∀ i, term ∈ {0, A.tm}` on the ABSTRACT nodes — concrete
  terms follow through s1Agrees/shellSync); net half in `NetCorr`
  (`netTerms`: every live message's term = EXACTLY `A.tm` —
  STRONGER than the amendment's "∈ {0, tm}" spelling; justification
  in the clause docstring: send:562 term-stamping + no node emits at
  term 0; the exact form kills BOTH the `m.Term < r.Term` block and
  the spurious `m.Term == 0` local-prelude branch at deliveries).
  Establishable at the post-campaign loop head (chdriver:44 runs
  before the round loop; every net message then carries term 1).
- [AGENT] DESIGN DELTA against Amendment 1's letter, recorded not
  absorbed: (i) the amendment's chain "Next ≥ Match+1 ≥ 2" is
  unsatisfiable literally (follower Match=0 at reset) — `ProgOk`
  states the two bounds separately (`Next ≥ Match+1`, `Next ≥ 2`),
  which is what census §2.4 actually uses; (ii) `ProgOk.nextUB`
  (`Next ≤ lastIndex+1`) ADDED beyond the amendment's named facts —
  without it `term(Next-1)` can hit the ErrUnavailable arm
  (log.go:401-403) and `maybeSendSnapshot` is not refuted; the
  amendment's facts kill only the ErrCompacted route; (iii)
  `ProgOk.stateWire` (`State ∈ {0,1}`) added — the vocabulary the
  amendment names ("State incl. StateProbe") plus the fact the
  handler specs need to refute the StateSnapshot arms (census §2.6
  lists BecomeSnapshot unreachable). Each is preservable (reset
  re-establishes; MaybeUpdate/MaybeDecrTo respect the bounds;
  BecomeSnapshot has no reachable caller).
- [AGENT] Progress population facts added to `Pair.progress`
  (tracker keys = the voter set, both directions, lookup
  vocabulary): what kills `RawNode.Step`'s `pr == nil` arm
  (rawnode.go:118-120) and `stepLeader:1397`'s nil arm — cheap here,
  consumed by clusters C/D/E.
- [AGENT] U3.0d reader extension placed IN `AbsTwinCheckerRead.lean`
  (the U3.0b file, per the brief's option): `absProgressOf` (raft
  cell → embedded trk → Progress map → per-id AbsProgress incl.
  Inflights count/size) + `absRaftLogOf` (raft cell → raftLog hop →
  the LANDED `absRaftLog` view — the concrete log-length axis).
  New σ-DEPENDENT map lens `mapReadD`/`mapPairsD` (the Progress
  map's values are pointers; the landed pure-decoder `mapRead`
  cannot read through them) — kept BESIDE `mapRead`, not replacing
  it (three landed pure consumers untouched); promotion of the pair
  into one generalized lens recorded as a candidate at the third
  map-reader class. `_ren` congruences composed from the lens laws
  for all of it; `ProgressShaped` + `absProgressOf_defined`
  definedness spine; non-vacuity 4-cell state `wProgState`
  (wProg_read computes; wProg_shaped discharges). `absRaftLogOf`
  definedness enters through the invariant's ∃-equation form (the
  same posture as `absTwinNodeRaft`, which has no Shaped spine).
- [AGENT] POPULATION TIGHTENED (Amendment 1 item 3): `NetCorr`'s
  population clause now lists the census-proved four wire types;
  the design note's five-type list (incl. Prop(local)) is corrected
  ON THE RECORD (clause docstring cites census §3.1 and the
  unreachable forwarding site). `msgProp` constant retained (the
  D-cluster's local-message vocabulary).
- [AGENT] C5/U4 VERDICT (Amendment 1 item 4): NO amendment needed —
  recorded at `I`'s docstring. The state-level Stream clause
  (`ch <:+ ch₀`) is draw-count-agnostic and the span judgment's
  ∀ch/suffix discipline constrains nothing about a dead draw's
  value; the landed demonstration is `becomeFollower_callSpec`
  itself, whose span already consumes the D-11 jitter draw
  (becomeFollower → reset → resetRandomizedElectionTimeout) with a
  value-agnostic statement.

## U3.0d — THE CENSUS ADDENDA FOLDED INTO `I`: LANDED

- Files: `Specs/Raft/AbsTwinCheckerRead.lean` (+~330 lines: reader 6
  section, mapReadD lens, _ren + definedness + non-vacuity),
  `Specs/RaftPilot/Invariant.lean` (AbsCarrier.tm; ProgOk;
  Pair.tmPos/terms/progress; NetCorr population four-type +
  netTerms; Elected branch pinned at A.tm; sanity lemmas
  `Pair.term_le`, `NetCorr.net_term_pos`; `lookupI` hoisted to the
  vocabulary section; module docstrings carry the U3.0d record).
- Zero True stubs (unchanged); definitions + cheap sanity lemmas
  only; hatch grep over both touched files: 0
  sorry/native_decide/partial.
- Builds: `AbsTwinCheckerRead` target 43 jobs EXIT=0 (0.76 s
  module); `Invariant` target 59 jobs EXIT=0 (0.85 s module);
  **wave-boundary FULL proofs build (box lock held + released):
  EXIT=0, 537 jobs, wall 4.88 s (warm tree), peak RSS 2.2 GB**
  (artifacts/w3/u30d-full-build.log). No differential owed
  (proofs/docs only).

## Judgment calls — U3.1-F

- [AGENT] THE RESULT-BEARING JUDGMENT FORM (`CallSpecR`,
  `SpecJudgment.lean`): the entire F family returns values, and W1's
  `CallSpec` is resultless — its sealed refusal
  (`refusalResultBearingCallSpan`) named exactly this consumer. The
  landed form is CALLEE-LOCAL: the span ends at RETURN ARRIVAL
  (`.returning (.frame plans env rlocs [] k false)`) — one machine
  step BEFORE the result read (`loadMany`) and the caller-side
  `tgtOpK` target-operand walk — with the results delivered as a
  `loadMany` equation the call site's next step consumes
  definitionally. ∀ plans/env/k: the target plans ride the frame
  inertly, so the W1 open-tail route extends to them WITHOUT any
  plug-walk change (the span never crosses the barrier frame's
  exit). The seal's docstring now scopes it to the caller-inclusive
  form only. Rules: `CallSpecR.conseq`, `CallSpecR.consume`.
  LINEAGE in the docstring (Hoare procedure rule with result
  substitution at the CPS presentation).
- [AGENT] THE F PROOF PATTERN (measured, first two members): spec at
  the CANONICAL COMPLIANT placement (footprint cell at `.base ⟨31⟩`,
  first address above the twin's 31 forced-identity globals; twin
  tables pinned; `nextAddr` concrete) over an EXACT footprint family
  whose UNREAD positions are FREE `GoValue`/`Option Ty` parameters
  (maximal width — any value rides opaquely) and whose read
  positions pin only the constructors the span scrutinizes. The
  whole span then closes by ONE `kernel_rfl` at open
  `plans`/`env`/`k`. Empirical span discovery by a step-trace probe
  (artifacts/w3/ProbeSpan*.lean) before stating the theorem — the
  probe supplies the step count, allocation addresses, and terminal
  cells; the kernel re-checks all of it symbolically.
- [AGENT] THE MECHANISM BLOCKER, derived and recorded (the park
  line for the rest of the cluster): kernel reduction decides a
  data branch only when it bottoms out on constructors. Two
  universal stuck classes hit here:
  (i) store-time `IntKind.normalize` on a symbolic scalar makes any
  subsequent branch on that scalar kernel-stuck (maybeLastIndex's
  nonempty arm: the length is stored into the `l` local normalized,
  then `l != 0` cannot reduce for free `k`);
  (ii) `validateSlice`'s `len > cap` is a Nat-Nat comparison —
  `Nat.ble` recurses on BOTH constructors, so it reduces ONLY when
  one side is a literal (len 0 passed; len `m+1` vs any symbolic cap
  is stuck), which blocks EVERY symbolic-length slice length/index
  read (MemoryStorage.firstIndex's `ents[0]` included).
  The needed mechanism is the bf pattern at DATA branches: split the
  span into windows at the stuck step and cross with a
  hypothesis-consuming step lemma (`hlen`-style range/branch
  premises — exactly the shape of bf's normalize premises and
  stream crossings). This is a PROMOTION-LEDGER candidate kit
  ("data-branch crossing lemmas": ifK-on-symbolic-bool,
  normalize-collapse under range premises, validateSlice under a
  well-formedness premise) with ~everything in the cluster as its
  consumers — the general form is mandatory under the middle path
  (COST × CONSUMER COUNT both high). NOT built this session:
  building it well is a focused unit of its own, and landing it
  half-made to rescue one more member would be the wrong side of
  park-not-weaken.
- [AGENT] Coverage labeling instead of conclusion weakening: the
  `maybeLastIndex` member is scoped to the empty-unstable,
  live-backing-slice sub-family and SAYS SO (partial coverage
  labeled at birth; the nonempty arm parked on the crossing kit;
  the nil-slice sibling recorded as a consumer-demand variant).
  Conclusions are the subject's exact arm results — nothing
  narrowed silently.
- [AGENT] Box note: an unrelated project ran its own capped 48G
  build concurrently during the wave-boundary build; both builds
  capped 48G (2×48 < 125G — the parallel-lane cap discipline);
  golean's box-wide lock held by this lane throughout.

## U3.1-F — THE SHARED LOG/UTIL LAYER: PARTIAL (judgment form + 2 members LANDED; remainder PARKED with records)

- **LANDED:**
  * `CallSpecR` + `conseq`/`consume` (`GoLeanProofs/SpecJudgment.lean`;
    the sealed refusal rescoped to the caller-inclusive form).
  * `Specs/RaftPilot/LogReadSpecs.lean` (new; registered in
    `proofs/GoLeanProofs.lean`): the footprint-family formers
    (`unstableV`/`logCellV`/`uFam`, receiver `uArgV` = the interior
    `&l.unstable` field loc), and
    - `unstable_maybeFirstIndex_callSpecR` — the FULL T1 family
      (snapshot nil, everything else free incl. the entries
      descriptor): returns `(0, false)`, footprint read back
      unchanged; private 38-step span `uFI_span` (kernel_rfl, zero
      choices, open plans/env/k);
    - `unstable_maybeLastIndex_empty_callSpecR` — the
      empty-unstable live-backing member (labeled partial
      coverage): returns `(0, false)`; private 69-step span
      `uLI0_span` (exercises local-decl allocation + the length
      read + validateSlice at len 0);
    - `uFIPre_inhabited` (the ∃-discharge; the judgment form's
      non-vacuity instance is the subject spec itself).
  * Every export count-free; step counts/addresses live only in the
    private span lemmas + this log (W1 convention).
- **PARKED, with records (charter park-not-weaken):** the remaining
  family members —
  * `unstable.maybeLastIndex` nonempty arm + `maybeTerm` (+ the
    unstable slice/mustCheckOutOfBounds pair): data branches on
    normalized symbolic scalars → the crossing kit (blocker (i)/(ii)
    above). maybeTerm additionally branches `i < offset` on two free
    Ints — pure crossing-kit content.
  * `MemoryStorage.{firstIndex,lastIndex,Term,Entries,FirstIndex,
    LastIndex}` (the storage read half incl. the Lock/defer walk):
    `ents[0]`/`ents[i-offset]` symbolic-length slice indexing →
    blocker (ii); the lock walk itself is concrete-reducible (sync
    payload pinned unlocked) and composes via `CallSpecR.consume`
    once the leaves exist. Probe bodies read
    (artifacts/w3/ProbeMS.lean output): firstIndex is
    two-statement + one nested `GetIndex` call — the cheapest
    post-kit member.
  * `raftLog.{term,entries,slice,firstIndex,lastIndex,matchTerm,
    zeroTermOnOutOfBounds,maybeCommit-adjacent reads}` +
    `mustCheckOutOfBounds` (U3 range obligations): compose the
    above via `CallSpecR.consume` + the crossing kit; `slice`'s
    mixed storage+unstable slow path (census U1, costed reachable)
    additionally consumes the W2 loop rules through `extend`'s
    append loop — the single costliest member, unchanged verdict.
- **Builds:** LogReadSpecs module 13 s (one span) → 26 s (both
  spans) at 48G target builds; **wave-boundary FULL proofs build
  (lock held + released): EXIT=0, 538 jobs, wall 65 s (new module
  cold), peak RSS 6.9 GB**
  (artifacts/w3/u31f-full-build.log/.time). Hatch grep over
  SpecJudgment/LogReadSpecs: 0 sorry/native_decide/partial. No
  differential owed (proofs/docs only); no Audit/*, no scripts/*,
  no GoCore, no baselines touched; `proofs/GoLeanProofs.lean`
  gained one proof-layer import.

## WAVE CHECKPOINT (U3.0d + U3.1-F; branch-complete for this session)

- U3.0d LANDED (fc10a11d). U3.1-F PARTIAL as recorded above (this
  commit): the result-bearing judgment layer + the F proof pattern
  demonstrated end-to-end on two subject members; the remainder
  parked on ONE named mechanism (the data-branch crossing kit) —
  the recommended next unit for the cluster, before any further
  member is attempted.
- Census claims re-verified where built upon (U3.0d entry above);
  the wire probes (function ids, typeDefs for
  raftLog/unstable/MemoryStorage/Entry/tracker, the lowered bodies
  of the specced members) all agree with the census's reachable set
  and the invariant's vocabulary.
- The two retained interface witnesses: GREEN throughout (in every
  full-target build).
- FOR THE LANDING AUDIT (restated from Wave 3.0, still standing):
  the W2.5 [AGENT] adjudication that adopted the invariant design is
  a mandatory [USER] review item. New from this session: nothing
  trust-adjacent touched; the U3.0d design deltas vs Amendment 1
  (ProgOk.nextUB, stateWire, netTerms-exact, the distributive
  reading of the amendment's Next-chain) are flagged for review in
  the U3.0d entry.

---

# W3 continuation (2026-08-27) — THE DATA-BRANCH CROSSING KIT + U3.1-F completion (one writer; the U3.1-F worker's successor on the same lane)

Charter: the coordinator's crossing-kit brief (kit as a mechanism
unit + un-park the U3.1-F remainder). Design note:
`docs/2026-08-27_crossing-kit-design.md` (LINEAGE + quantifier-audit
line there; the kit advances ∀-state at spec boundaries by case
analysis over the path condition — the split is over the program's
own branch structure, never a subject run).

## Successor re-verification (the park record's stuck-goal claims,
REPRODUCED before design — the brief's precondition)

- Tip + cleanliness: `fe4e42a3`, clean. CONFIRMED.
- Blocker (ii) REPRODUCED (`artifacts/w3/kit-stuck1.out`):
  `validateSlice ⟨some b, 0, k+1, sc⟩` does not reduce at free
  `k`/`sc` (the reducer diverges through the refusal message's
  `Nat.repr` on the undecidable `len > cap`); the len-0 control
  reduces to `.ok ()` — exactly the landed empty member's escape.
- Blocker (i) REPRODUCED (`artifacts/w3/kit-stuck2.out`):
  `IntKind.normalize .int (Int.ofNat (k+1))` (and the branch bool
  over it) does not reduce at free `k`.
- Kit-lemma shape probe (`artifacts/w3/kit-lemmas.out`): the class-A
  crossing (`subst`+`rfl`), the class-B unfold-to-match `rfl` +
  `rw`, and the `validateSlice` collapse all PASS at abstract σ; the
  normalize collapses need core-tactic proofs (no Mathlib in this
  tree — `norm_num` absent; `omega` + `Int.emod` route landed).

## Judgment calls — the kit

- [AGENT] The kit EXTENDS StepKit's conditioned-step idiom instead
  of duplicating it: `stepFn_strict_apply` (already landed, promoted
  ≥2 rule) is the class-B workhorse; the kit adds the VALUE-level
  path-condition lemmas that feed it (`validateSlice_ok`,
  `applyStrict_length_slice`, `applyStrict_indexGet_slice`,
  `applyStrict_deref`, `loadLoc_base`), the class-A branch step
  lemmas (`stepFn_ifK_true/false`), and the normalize collapse
  family (`normalize_int_eq`/`normalize_uint64_eq` + `ofNat`
  corollaries, literal-bound hypotheses so consumers discharge by
  `omega`). New module `proofs/GoLeanProofs/Sym/Crossing.lean`
  (~200 lines), registered in `proofs/GoLeanProofs.lean`.
  `whileK`/`andK`/`orK` siblings NOT built (no consumer in this
  unit; consume-on-demand, recorded in the design note).
- [AGENT] The window-split convention (measured on the first
  consumer): span = `kernel_rfl` windows chained by
  `stepFnIter_chain`; crossings as `stepFnIter_one` of a
  conditioned step; hypothesis REWRITES of window exits between
  links (a collapse rewrite often makes the following branch
  SELF-reducing — maybeLastIndex's `l != 0` needed no ifK lemma at
  all after the normalize collapse). Probe-first per member (config
  dumps at the stuck boundaries: `artifacts/w3/ProbeKitLI*.lean`).

## THE CROSSING KIT: LANDED (build 13 jobs, module 0.3 s)

## U3.1-F un-parking — `maybeLastIndex` COMPLETE (first two kit
consumers)

- `unstable_maybeLastIndex_nonempty_callSpecR` — the parked nonempty
  arm: 3 windows (18/11/41 steps, private) + the length crossing
  (class 2) + normalize collapses (class 1); range premises
  reader-vocabulary (`len ≤ cap`, `len < 2^63`, offset bounds);
  returns `(offset + len - 1, true)`, footprint unchanged. Module
  build 42 s (both new spans in-module). FIRST BUILD GREEN — the
  kit's window statements + crossing lemmas composed without
  rework.
- `unstable_maybeLastIndex_callSpecR` — THE JOIN (recombination):
  full T1-family coverage at any length `n` by constructor-complete
  case analysis (`0` vs `kn+1`), citing the two arm members through
  `CallSpecR.conseq`; the empty member's partial-coverage label is
  UPGRADED here (the labels on the arm members stand as arm-scoped
  statements, not coverage gaps).

## U3.1-F un-parking — `maybeTerm` COMPLETE at the T1 family (arms
= the program's own branch trichotomy)

- [AGENT] Wire fact found by the probe and folded into the family:
  `raftpb.Entry`'s proto-optional fields are POINTERS in the pinned
  wire (`Term : *uint64` — `GetTerm` nil-checks then derefs); the
  in-range family pins entry/Term cells at canonical 32-34 with free
  payloads, and the backing-array read outcome is a family-carried
  hypothesis (`hget` — classic symbolic-memory read).
- [AGENT] COMPOSITION FINDING (costing-relevant, recorded): within-
  family composition INLINES the callee — `maybeTerm`'s ≥offset arms
  re-walk `maybeLastIndex` at the caller's extended heap (the landed
  leaf CallSpecR is exact-heap and cannot be `consume`d mid-span at
  a wider state; the alternative is the W2 FrameSim+plug transport,
  the expensive road). The callee's two crossings simply RECUR and
  are crossed by the same kit pieces — cost is additive windows, no
  new mechanism. Cluster costing must price composed members as
  window-sum, not consume-hops.
- Members (all exported count-free; range/read premises in reader
  vocabulary):
  * `unstable_maybeTerm_below_callSpecR` — compacted arm (i <
    offset): 2 windows + ONE class-A crossing (`stepFn_ifK_true` +
    `decide_eq_true` — the kit's genuinely-symbolic two-scalar
    comparison consumer); cells 32-34 ride free.
  * `unstable_maybeTerm_aboveLast_callSpecR` — out-of-range arm:
    5 windows (13/28/11/64/25) + 3 crossings (two class-A + the
    inner length read) + the full collapse chain (the inner call's
    result monster: 4 nested normalizes, 5-rewrite chain).
  * `unstable_maybeTerm_inRange_callSpecR` — the unstable-read arm:
    6 windows (13/28/11/64/23/73) + 4 crossings (+`applyStrict_
    indexGet_slice` under `hget`); returns `(entry.Term, true)`.
- Per-member join NOT built ([AGENT]): a trichotomy join needs
  per-index read facts for every in-range slot (an entries table the
  invariant carries); consumers (raftLog.term's arms) know their
  side, so the join is consumer-demand — recorded, not
  manufactured. The maybeLastIndex join stands as the kit's
  recombination witness.
- Builds: arm A module build 52 s; +arm B 65 s; +arm C 76 s (module
  total with all 11 span windows; target-build logs
  artifacts/w3/kit-mt*-build*.log).

## COSTING SIGNAL for the remaining Wave 3.1 clusters ([AGENT]
estimate, derivation-anchored to the PREDECESSOR session's
measurements — superseded by this session's kit-adjusted signal at
the end of this log)

Measured data: straight-line/pinned-branch member ≈ one probe + one
kernel span theorem (13 s build; ~1-2 h agent time end-to-end);
the judgment layer amortized (done); data-branch members blocked on
the crossing kit (est. one focused unit: ~10-15 conditioned step
lemmas in the StepKit idiom + the window-split convention — the
highest-leverage next build, ~every remaining member its consumer).

- **F remainder** (~20 fns): crossing kit first, then mostly
  2-4-window members; `slice` slow path adds loop-rule composition.
  Multi-session (3-5 Fable worker-days) after the kit (kit itself
  ~1 day-class).
- **B (harvest engine)**: Ready/readyWithoutAccept/acceptReady/
  Advance are multi-call bodies over rawnode state + storage
  Append/SetHardState (Append loops + lock walk). Needs F's storage
  half + the kit + loop rules; stepsOnAdvance's local-step replay
  makes Advance the widest span. ≈ 1.5-2× F-remainder.
- **C (election cluster)**: Step prelude case analysis is DIRECTLY
  served by U3.0d's term-bound clause (the m.Term<r.Term block and
  the local-prelude branch refute from `netTerms`+`terms`+`tmPos`);
  campaign/poll/becomeLeader are becomeFollower-class spans (the
  W1 pilot's cost datum: ~88 s-class windows each after fixture
  generation); TallyVotes/VoteResult iterate the votes map → W2 map
  loop rules. ≈ F-remainder class overall.
- **D (replication cluster)**: handleAppendEntries all three exits
  (R1) + maybeAppend/findConflict/truncateAndAppend — entry-list
  loops throughout → loop rules + kit; commitTo's U3 range
  obligation consumes `ProgOk`/log facts. With E the largest; the
  three-exit case analysis triples the window sets.
- **E (ack/commit cluster)**: stepLeader's MsgAppResp case is the
  census's costliest single unit (194 lines live, both arms, probe
  state machine + Inflights + maybeCommit/bcastAppend composition);
  needs D's send/append specs + F + kit. Largest single unit;
  schedule last as the charter's order already does.
- **A (init cluster)**: 14+1 confchange fns + newRaft/validate +
  MemoryStorage init: mostly straight-line at a PINNED config shape
  (the config literal is reflected-program text) → today's cheap
  pattern applies widely; newRaft's whole-chain span is long but
  branch-poor. Cheapest per function; good parallel filler.
