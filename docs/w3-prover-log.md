# W3 log (2026-08-27) — one writer: the w3 Wave-3.0 worker (same lane, W2's successor)

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
