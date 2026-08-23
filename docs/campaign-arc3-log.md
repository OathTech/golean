# Campaign Arc 3 log — refined_raft_net_invariant port

Branch `campaign-arc3`, worktree `.claude/worktrees/campaign-arc3`,
opened from f64d9b21. Governing document:
`docs/2026-08-21_raft-proof-constitution.md` (§5 Plan A — the Verdi
STRUCTURE port; §3 inviolables; §4.1 surgery threshold). One writer:
this lane's worker. Unit: the ghost-layer invariant principle
(`refined_raft_net_invariant`) — groundwork for the invariant network
T1's proof rides. Deliverables per the unit charter: the port design
doc, `compat/verdi/VerdiCompat/RefinedProofStructure.lean` (zero
sorry), green `scripts/ci` (docs + compat/** only, so
`GOLEAN_ALLOW_NO_DIFF=1`).

Conventions: `[AGENT]` = judgment call made under §5 latitude, logged
not pre-approved. Checkpoints every ≤5 units of work, numbers
recomputed at the checkpoint, never restated.

## Entries

- 2026-08-22 [AGENT] Primary-source reading done from the MAIN
  checkout's `deps/verdi-raft` @ a3375e8 + `deps/verdi` @ 7e1641b
  (this worktree's `deps/` lacks both; the pin was verified by
  `git rev-parse` before reading; deps stay read-only — no
  `setup-deps` run needed since compat/verdi's build needs no deps
  checkout and the verdi checkouts are reference-reading only).
- 2026-08-22 [AGENT] File name: keep the charter's default
  `RefinedProofStructure.lean`, parallel to `ProofStructure.lean`.
  Upstream splits the material across `Raft/RaftRefinementInterface.v`
  (defs + interface class) and `RaftProofs/RaftRefinementProof.v` (the
  proofs); we merge them in one file because Lean needs no
  interface-class indirection — we prove the principle directly, as
  ProofStructure.lean already does for the base layer. Source-line
  citations in docstrings keep the 1:1 map recoverable.
- 2026-08-22 [AGENT] Scope call: port the ghost layer RAFT-SPECIFIC,
  inlining Verdi's generic `GhostSimulations.v` construction at its
  single Raft instance instead of porting the `GhostMultiParams`
  typeclass layer. Reasons: (a) Arc 3 has exactly one ghost instance
  (`electionsData`); the msg-ghost layer (`RaftMsgRefinementInterface`,
  for the GhostLog* chain) is a LATER, different construction and can
  motivate a generic lift when it arrives (promotion-ledger rule: lift
  at ≥2 consumers); (b) Coq's generic layer pays for itself via
  `TotalMapSimulations` reuse, which we are not porting — the Lean
  proofs of the two simulation directions are direct inductions either
  way. Recorded as design-doc §5 D1.
- 2026-08-22 [AGENT] RRIR constructor shape: mirror the base port's
  style (pair projections `(net.nwState h).1/.2` inline where Coq
  threads `nwState net h = (gd, d)` equations through constructor
  premises) — Lean's definitional pair eta makes them equivalent and
  it matches the sibling file's ported `RIR_doLeader`. The OBLIGATION
  definitions keep Coq's exact premise shapes (explicit `gd`/`d` with
  equation premises), since those are the interfaces ~73 verdi-raft
  proof files instantiate — 1:1 there is what makes chain porting
  mechanical. Recorded as design-doc §5 D2.
- 2026-08-22 Slice 1 committed (d60a5b40): this log + the port design
  doc. Baseline `lake build` of compat/verdi (capped, 24G) green
  before any edit: AxCheck sweep 840 declarations.
- 2026-08-22 Slice 2: RefinedProofStructure.lean part 1 —
  `electionsData`, `elections_ghost_init`, the five
  `update_elections_data_*` ghost handlers + net/input dispatchers,
  the refined parameter triple, `refined_raft_intermediate_reachable`;
  wired into `VerdiCompat.lean` so the enforcing AxCheck sweep covers
  the module from birth (sweep now 918 declarations, build green).
  [AGENT] Two upstream pattern subtleties preserved and
  docstring-flagged: `update_elections_data_appendEntries` binds the
  REPLY's `t`/`entries` (Coq shadows the request's; named `t'`/`es'`
  here), and the `_net` dispatcher passes `src` for BOTH `src` and
  `candidateId` at the RequestVote arm (upstream's exact call,
  `RaftRefinementInterface.v:94-95`), keeping the unused
  `candidateId` parameter so obligation statements stay 1:1.
- 2026-08-22 Slice 3: the 11 obligation shapes
  (`RaftRefinementInterface.v:211-325`, premise shapes 1:1 incl. the
  `gd`-equations), the two dispatchers, and THE principle
  `refined_raft_net_invariant` re-proved from scratch
  (`RaftRefinementProof.v:56-194`). Build green, AxCheck sweep 934
  decls, zero sorry (grep clean). [AGENT] Proof shape mirrors the
  sibling's assert-chain (two intermediate RRIR states per
  step-failure handler case) with the ghost threaded through both
  updates via `update_same`/`update_update_same`; the ghost handlers
  needed no lemmas of their own — the principle is ghost-generic
  exactly as upstream's. Dispatcher `gd`s are instantiated with the
  `update_elections_data_net/_input` dispatcher term and the per-case
  equation discharged by `rw [hbody]; rfl` (constructor iota).
- 2026-08-22 Slice 4: erasure — `deghost_packet`/`deghost`/`deghost_spec`,
  helpers `update_snd`/`network_eq_mk`/`deghost_send_packets`,
  `ghost_simulation_1` (refined step_failure projects to base, direct
  case analysis instead of Coq's TotalMapSimulations route — D1),
  `simulation_1` (RRIR → RIR of the deghost), `lift_prop`. Build green.
  [AGENT] Elaboration gotcha recorded for successors: base
  `step_failure` constructors whose FIRST explicit arg is a node name
  (`StepFailure_input/_fail/_reboot`) pin the implicit `M` to the
  refined instance when the name variable comes from a refined
  context — pass `(M := raft_multi_params (P := P))` explicitly.
- 2026-08-22 Slice 5: reghosting — `ghost_packet` (round trips with
  `deghost_packet` definitional by structure eta), `map_eq_append_cons`
  (the bag-delivery inversion), `ghost_send_packets`,
  `ghost_simulation_2` (the constructed direction: the ghost successor
  is built per step case), `simulation_2` (every base-reachable net IS
  a deghosted ghost-reachable net), and `lower_prop` — THE transfer
  principle (`RaftRefinementProof.v:507-609`). Build green, AxCheck
  sweep 954 decls.
- 2026-08-22 CHECKPOINT (5 slices, numbers recomputed from this tip's
  build/git, not restated): commits d60a5b40, 1b6aff9b, c99be3c1,
  e9e56489 + this slice; `lake build` (capped 24G) green; AxCheck
  sweep says 954 declarations, axiom set within [propext, Quot.sound];
  `grep -n "sorry\|native_decide"` over RefinedProofStructure.lean:
  zero hits. Remaining in-unit work: the discharge witness (GAP-3
  companion), AxCheck curated pins for the new headliners, scripts/ci.
- 2026-08-22 Slice 6: the discharge witness (constitution §3.3 /
  CLAUDE.md witness gate) — `VotesShape` (`votes`/`votesWithLog`
  extended in lockstep by every ghost handler), five per-handler
  preservation lemmas, and `refined_votes_shape_witness` instantiating
  the principle with ALL eleven obligations discharged. [AGENT]
  Witness choice: a real (if small) ghost invariant rather than
  `fun _ => True`, so the obligation premises (handler equations, `gd`
  equations, state-update conditions) are all actually consumed;
  deliberately NOT one of the election-safety chain's invariants, to
  avoid pre-empting unit 2's 1:1 statements. Plus AxCheck curated pins
  for refined_raft_net_invariant / simulation_1 / simulation_2 /
  lift_prop / lower_prop / refined_votes_shape_witness (gate
  strengthening only; captured from a fresh `#print axioms` run — all
  [propext, Quot.sound]). Full build green: AxCheck sweep 987 decls,
  diffharness fixture pin OK (320 cases), zero warnings after
  `omit O in` on the five lemmas.
- 2026-08-22 Final gate: `GOLEAN_ALLOW_NO_DIFF=1 GOLEAN_MEM_MAX=24G
  scripts/ci` from the worktree root — **RESULT: PASS, exit 0**
  (log: `artifacts/ci-arc3.log`, gitignored). All steps ok; the two
  no-diff notes are the explicitly-allowed docs+compat-lane hatch
  (this arc touched only `compat/verdi/**` + `docs/campaign-arc3*` +
  `docs/2026-08-22_campaign-arc3-*`; no runtime code, so no
  differential owed). [AGENT] The ci run printed the report-only
  comparator-landmark staleness note ("last certified run 56 theorems
  @ 1730567a2d3f, 10 commit(s) ago"). Per the widened trigger that
  note obliges a `comparator-judge` run at MERGE time; this unit ends
  branch-complete without merging (constitution §4.1 — merge is
  Mike's), nothing here touches a designated headline statement or
  Challenge's trusted closure (the statement-TCB closure step passed),
  so the judge run is left to the operator's merge step and flagged
  here rather than run out-of-band.

## Final entry — unit complete (2026-08-22, tip 58146125 + this log commit)

**Proved at tip**, all in
`compat/verdi/VerdiCompat/RefinedProofStructure.lean` (1341 lines,
zero `sorry`/`native_decide` — grep clean; enforced by the in-build
AxCheck sweep, 987 declarations within [propext, Quot.sound], plus six
new curated `#guard_msgs` pins). `#print axioms` verbatim (captured
from a `lake env lean` run of the built package):

```
'VerdiCompat.Raft.refined_raft_net_invariant' depends on axioms: [propext, Quot.sound]
'VerdiCompat.Raft.simulation_1' depends on axioms: [propext, Quot.sound]
'VerdiCompat.Raft.simulation_2' depends on axioms: [propext, Quot.sound]
'VerdiCompat.Raft.lift_prop' depends on axioms: [propext, Quot.sound]
'VerdiCompat.Raft.lower_prop' depends on axioms: [propext, Quot.sound]
'VerdiCompat.Raft.refined_votes_shape_witness' depends on axioms: [propext, Quot.sound]
'VerdiCompat.Raft.deghost_spec' depends on axioms: [propext, Quot.sound]
```

The inventory (file line numbers at this tip):
- ghost vocabulary: `electionsData` (:51), the five
  `update_elections_data_*` handlers + net/input dispatchers, refined
  parameter triple, `refined_raft_intermediate_reachable` (:252);
- the eleven obligation shapes (1:1 premise shapes) + dispatchers
  (:423, :491) + **`refined_raft_net_invariant`** (:515) — THE
  ghost-layer induction principle;
- erasure/transfer: `deghost` (:759), `deghost_spec` (:763),
  `ghost_simulation_1` (:782), `simulation_1` (:847), `lift_prop`
  (:919), `ghost_simulation_2` (:983), `simulation_2` (:1057),
  **`lower_prop`** (:1155) — the transfer principle;
- discharge witness: `VotesShape` (:1173) +
  `refined_votes_shape_witness` (:1239), all eleven obligations
  discharged on a concrete invariant.

**Honestly open (numbered gaps; none counted toward any total):**
- GAP-1: the primed obligation variants
  (`refined_raft_net_invariant_*'`, `RaftRefinementInterface.v:327-439`)
  and `refined_raft_net_invariant'` (`RaftRefinementProof.v:196-427`)
  are NOT ported — they add post-state-reachability premises used by a
  minority of chain files; known-shape repeat, port on first need.
- GAP-2: the msg-ghost layer (`RaftMsgRefinementInterface.v`, per-packet
  ghost for the GhostLog* chain) is not ported — a different
  construction, later arc (design doc §5 D1).
- GAP-3: no election-safety chain invariant is instantiated yet — this
  unit is the principle + transfer machinery only; the witness is a
  deliberately-off-chain invariant.

**Next unit's charter (Arc 3, unit 2):** port the election-safety chain
bottom-up per design doc §3/§4 — `votes_le_currentTerm` (ghost,
rri-only, smallest) → `votes_correct` → `candidates_vote_for_selves`
(BASE, exercises the already-ported base principle) → then unit 3:
`cronies_correct` and `one_leader_per_term` via `lower_prop`, porting
`wonElection_one_in_common` (CommonTheorems.v) alongside. Statements
1:1 from the interface files in the design-doc §3 table; helper
SpecLemmas ported on demand only.

## Unit 2 — the election-safety chain (2026-08-22, coordinator-accepted charter)

Coordinator ruling folded in: unit 2 now spans the WHOLE chain
(`votes_le_currentTerm` → `votes_correct` →
`candidates_vote_for_selves` → `cronies_correct` →
`one_leader_per_term`, headline via `lower_prop`); GAP-1 primed
variants ported on first genuine need; any harness/twin-vocabulary
need is a numbered Arc-4-seam gap, never invented statement-side.

- 2026-08-22 SUCCESSOR RE-VERIFICATION of unit 1's top claims
  (recomputed, not restated): fresh capped `lake build` at 4bbcf5fc —
  green, `AxCheck sweep: 987 declarations across VerdiCompat modules,
  axiom set within [propext, Quot.sound]`; fresh `lake env lean`
  #print axioms: `refined_raft_net_invariant`, `lower_prop`,
  `refined_votes_shape_witness` all `[propext, Quot.sound]`;
  `grep -n "sorry\|native_decide\|^axiom\| axiom "` over
  RefinedProofStructure.lean: exactly one hit, line 744, docstring
  prose ("the lane's recorded axiom set") — zero hatches. Claims
  hold; building on them.
- 2026-08-22 Slice 7 (unit 2): `ElectionSpecLemmas.lean` — the
  SpecLemmas.v/RefinementSpecLemmas.v slices the chain uses. [AGENT]
  Style call (docstring-flagged in the file): ONE comprehensive cases
  lemma per handler (advanceCurrentTerm, handleClientRequest,
  handleTimeout, handleAppendEntries[Reply], handleRequestVote[Reply],
  doLeader, doGenericServer + cacheApplyEntry/applyEntries) subsuming
  the upstream single-fact lemmas each docstring cites, plus the
  votes-focused ghost-update lemmas (client_request/appendEntries/
  requestVoteReply unchanged-fields; requestVote votes elim/old/intro;
  timeout votes elim/intro). [AGENT] handleTimeout_spec's candidacy
  branch carries `st.type ≠ .Leader` (the branch trigger) — needed by
  `update_elections_data_timeout_votes_intro`, where upstream's Ltac
  gets it implicitly from the shared scrutinee. Build green, AxCheck
  sweep 1064 decls (was 987).
- 2026-08-22 Slice 8 (95d2fb0a): `ElectionSafety.lean` —
  `votes_le_currentTerm` + `votes_correct` (statements 1:1 with
  VotesLeCurrentTermInterface.v:9-13 / VotesCorrectInterface.v:8-28)
  proved through `refined_raft_net_invariant`. [AGENT] Plumbing call:
  all three votes_correct conjuncts are pointwise over nodes, so a
  node-level bundle (`votes_state_ok`) + one step helper
  (`votes_correct_of_update`) replaces upstream's per-obligation Ltac
  (`update_destruct; rewrite_update`); per-handler node cores are
  private lemmas each citing its VotesCorrectProof.v range. Sweep 1087.
- 2026-08-22 Slice 9 (b4439001): `candidates_vote_for_selves` (BASE
  layer, CandidatesVoteForSelvesInterface.v:8-11) — first real
  instantiation of the base `raft_net_invariant` from
  ProofStructure.lean. [AGENT] Added
  `handleAppendEntries_reject_of_not_follower` to the spec lemmas: the
  blanket handler spec loses the branch correlation (accept ⇒
  follower), which upstream's `t`-Ltac gets by direct unfolding; the
  correlation lemma restores it once for both this proof and the
  coming cronies proof. Sweep 1099.
- 2026-08-22 CHECKPOINT (4 slices since last; numbers recomputed at
  b4439001): capped `lake build` green; AxCheck sweep prints 1099
  declarations, axiom set within [propext, Quot.sound]; grep
  sorry/native_decide over the three new files
  (ElectionSpecLemmas/ElectionSafety + RefinedProofStructure): 0 hits.
  Chain state: votes_le ✓, votes_correct ✓, candidates_vote_for_selves
  ✓; remaining: cronies_correct, one_leader_per_term (+ quorum
  counting lemmas), AxCheck pins, scripts/ci.
- 2026-08-22 Slice 10 (11c3204e): `cronies_correct_invariant` — the
  chain's heavyweight (CroniesCorrectInterface.v:9-33 1:1; upstream
  proof 718 lines). All four conjuncts through the refined principle;
  `votes_nw`'s tally case rides the consumed RequestVoteReply packet +
  `votes_correct_invariant`, exactly upstream's argument. [AGENT]
  cronies-side ghost lemmas added to ElectionSpecLemmas (elim/intro
  per handler, branch-correlated via `handleTimeout_not_leader` and
  the rvr type facts).
- 2026-08-22 Slice 11 (9c127a91): quorum counting + the exit theorem.
  `one_leader_per_term_ghost` (OneLeaderPerTermProof.v:25-54) and
  `one_leader_per_term_invariant` via `lower_prop` — ELECTION SAFETY
  at the base layer; also discharges `OneLeaderPerTermStatement`
  (Properties.lean's declared transfer target for election safety)
  natively, per the §9 translate-don't-certify route. [AGENT] TWO
  calls: (1) the counting layer (dedup lemmas, pigeon, div2_correct,
  wonElection_one_in_common — CommonTheorems.v:1376-1404, StructTact
  ListUtil.v:641-649) proved CONSTRUCTIVELY with a local `eraseOne`,
  because core's `List.erase` lemmas depend on Classical.choice and
  the lane's enforcing AxCheck sweep rejected them (the gate fired
  exactly as designed; recorded here as the gate's catch, not worked
  around by widening the axiom set — widening would be a recorded
  lane-doctrine decision, not mine). (2) `one_leader_per_term` was
  NOT redefined: the P1 statement port (Properties.lean:27) already
  has it 1:1; the chain proves that existing statement (a name
  collision the build caught).
- 2026-08-22 AxCheck curated pins added for the six chain headliners
  (votes_le / votes_correct / candidates_vote_for_selves /
  cronies_correct / one_leader_per_term invariants +
  oneLeaderPerTermStatement_holds), captured from a fresh
  `#print axioms` run — all [propext, Quot.sound]. Build green,
  sweep 1173 decls, diffharness fixture pin OK (320 cases), zero
  sorry/native_decide in both new files (grep).
- 2026-08-22 Unit-2 final gate: `GOLEAN_ALLOW_NO_DIFF=1
  GOLEAN_MEM_MAX=24G scripts/ci` — **RESULT: PASS, exit 0** (log:
  `artifacts/ci-arc3-unit2.log`, gitignored; the no-diff notes are the
  allowed docs+compat hatch — unit 2 touched only `compat/verdi/**`
  and this log). The report-only comparator-landmark note now reads
  12 commits stale — same operator-merge-time flag as unit 1; nothing
  in this unit touches a designated statement or Challenge's closure
  (statement-TCB step ok).

## Final entry — unit 2 complete (2026-08-22, tip ddba40b4 + this commit)

**Proved at tip** — the FULL election-safety chain, statements 1:1 with
their verdi-raft Interface files, proofs re-derived through the ported
principles, zero sorry/native_decide (grep; enforced by the in-build
AxCheck sweep: 1173 declarations within [propext, Quot.sound], plus six
new curated pins). `#print axioms` verbatim (fresh `lake env lean` run
against the built package):

```
'VerdiCompat.Raft.votes_le_currentTerm_invariant' depends on axioms: [propext, Quot.sound]
'VerdiCompat.Raft.votes_correct_invariant' depends on axioms: [propext, Quot.sound]
'VerdiCompat.Raft.candidates_vote_for_selves_invariant' depends on axioms: [propext, Quot.sound]
'VerdiCompat.Raft.cronies_correct_invariant' depends on axioms: [propext, Quot.sound]
'VerdiCompat.Raft.one_leader_per_term_invariant' depends on axioms: [propext, Quot.sound]
'VerdiCompat.Raft.oneLeaderPerTermStatement_holds' depends on axioms: [propext, Quot.sound]
```

Inventory (line numbers at this tip): `ElectionSpecLemmas.lean` (730
lines — handler cases lemmas + votes/cronies ghost facts, each
docstring citing the upstream lemmas subsumed);
`ElectionSafety.lean` (1766 lines): `votes_le_currentTerm_invariant`
(:36), `votes_correct_invariant` (:465),
`candidates_vote_for_selves_invariant` (:587, BASE principle),
`cronies_correct_invariant` (:720), constructive quorum counting
(`pigeon` :1649, `wonElection_one_in_common` :1698),
`one_leader_per_term_ghost` (:1722), **`one_leader_per_term_invariant`
(:1750)** — election safety at the base layer via `lower_prop` — and
**`oneLeaderPerTermStatement_holds` (:1759)**, discharging the P1
arc's declared transfer target natively.

**Coordinator-directed checks, resolved:** GAP-1 (primed obligation
variants) was NEVER TRIGGERED — no chain proof needed a primed
variant; it remains an open gap for later chains, not worked around.
No harness/twin-vocabulary need arose (the chain is entirely
ghost/base-side), so no new Arc-4-seam gaps.

**Honestly open (carried + new):**
- GAP-1 (primed variants) and GAP-2 (msg-ghost layer): unchanged.
- GAP-4 (new): the AxCheck sweep rejected core's classical
  `List.erase` lemmas; the constructive `eraseOne` replacement lives
  in ElectionSafety.lean. If a future chain needs heavier classical
  list machinery, the lane's axiom-set doctrine (propext/Quot.sound
  only) poses a recorded decision for the operator — flagged, not
  decided here.

**Next unit's charter (Arc 3, unit 3 — proposal):** the
leader-completeness approach chain per design doc §3's "beyond"
paragraph — `cronies_term` + `term_sanity` → `candidate_entries`
(CandidateEntriesProof.v, ghost `allEntries`/`leaderLogs` vocabulary)
— the entry ring of the T3 log-matching/leader-completeness lattice;
same conventions, spec lemmas on demand, primed variants on first
genuine need (GAP-1's charter).

## Unit 3 — the candidate_entries ring (2026-08-22, coordinator-accepted)

Scope: `cronies_term` + `term_sanity` → `candidate_entries` (the T3
leader-completeness lattice's entry ring). Coordinator additions:
running INVARIANT INDEX below (kept current every slice); GAP-2
msg-ghost ported on first genuine need only; checkpoints recomputed
from artifacts.

- 2026-08-22 SUCCESSOR RE-VERIFICATION of unit 2 (recomputed): fresh
  capped `lake build` at 1dbd15a6 green, `AxCheck sweep: 1173
  declarations ... within [propext, Quot.sound]`; fresh `#print
  axioms`: `one_leader_per_term_invariant` and
  `oneLeaderPerTermStatement_holds` both `[propext, Quot.sound]`;
  hatch grep over ElectionSafety/ElectionSpecLemmas: 2 hits, both
  docstring prose about the axiom set. Claims hold.

### INVARIANT INDEX (running; status at each update is build-verified)

| invariant | status | verdi source | ours |
|---|---|---|---|
| refined_raft_net_invariant (principle) | PROVED | Raft/RaftRefinementInterface.v:522 | RefinedProofStructure.lean:515 |
| lower_prop / lift_prop (transfer) | PROVED | RaftProofs/RaftRefinementProof.v:498,601 | RefinedProofStructure.lean:919,1155 |
| votes_le_currentTerm | PROVED | Raft/VotesLeCurrentTermInterface.v:9 | ElectionSafety.lean:36 |
| votes_correct | PROVED | Raft/VotesCorrectInterface.v:8-28 | ElectionSafety.lean:465 |
| candidates_vote_for_selves | PROVED (base) | Raft/CandidatesVoteForSelvesInterface.v:8 | ElectionSafety.lean:587 |
| cronies_correct | PROVED | Raft/CroniesCorrectInterface.v:9-33 | ElectionSafety.lean:720 |
| one_leader_per_term (ELECTION SAFETY) | PROVED (base, via lower_prop) | Raft/OneLeaderPerTermInterface.v:8 | ElectionSafety.lean:1750 (+ Statement :1759) |
| cronies_term | PROVED | Raft/CroniesTermInterface.v:9 | CandidateEntries.lean:43 |
| no_entries_past_current_term (term_sanity) | PROVED (base) | Raft/TermSanityInterface.v:9-24 | CandidateEntries.lean:220 |
| CandidateEntries | PROVED | Raft/CandidateEntriesInterface.v:10-24 | CandidateEntries.lean:808 (def :596) |
| requestVote_term_sanity | PROVED | Raft/RequestVoteTermSanityInterface.v:9 | LeaderLogs.lean:56 (invariant :64) |
| votes_votesWithLog_correspond | PROVED | Raft/VotesVotesWithLogCorrespondInterface.v:9-21 | LeaderLogs.lean:299 (invariant :366) |
| leaders_have_leaderLogs | PROVED | Raft/LeadersHaveLeaderLogsInterface.v:8 | LeaderLogs.lean:444 (invariant :451) |
| votedFor_term_sanity | PROVED | Raft/VotedForTermSanityInterface.v:8 | LeaderLogs.lean:640 (invariant :691) |
| requestVoteReply_term_sanity | PROVED | Raft/RequestVoteReplyTermSanityInterface.v:10 | LeaderLogs.lean (invariant, requestVoteReply_term_sanity_invariant) |
| requestVote_maxIndex_maxTerm | PROVED | Raft/RequestVoteMaxIndexMaxTermInterface.v:10 | LeaderLogs.lean (invariant, requestVote_maxIndex_maxTerm_invariant) |
| candidate_term_gt_log | PROVED (base) | Raft/CandidateTermGtLogInterface.v:8 | LeaderLogs.lean (invariant, candidate_term_gt_log_invariant) |
| leaderLogs_term_sanity (trio) | PROVED | Raft/LeaderLogsTermSanityInterface.v:9-24 | LeaderLogs.lean (three invariants, first real lift_prop consumer) |
| votedFor_moreUpToDate | PROVED | Raft/VotedForMoreUpToDateInterface.v:8-18 | LeaderLogs.lean (invariant) |
| requestVoteReply_moreUpToDate | PROVED | Raft/RequestVoteReplyMoreUpToDateInterface.v:9-21 | LeaderLogs.lean (invariant) |
| votesReceived_moreUpToDate | PROVED | Raft/VotesReceivedMoreUpToDateInterface.v:9-19 | LeaderLogs.lean (invariant) |
| leaderLogs_votesWithLog | PROVED | Raft/LeaderLogsVotesWithLogInterface.v:10-18 | LeaderLogs.lean (invariant) |
| one_leaderLog_per_term (+_log/_host) | PROVED | Raft/OneLeaderLogPerTermInterface.v:8-44 | LeaderLogs.lean (invariant + two corollaries) |
| **leader_completeness (LEADER COMPLETENESS, T3)** | PROVED | Raft/LeaderCompletenessInterface.v:9-42 | LeaderLogs.lean (defs) + LeaderCompleteness.lean (leader_completeness_invariant + both conjunct invariants) |
| every_entry_was_created (+ in_any_log field) | PROVED | Raft/EveryEntryWasCreatedInterface.v:9-37 | CreationRing.lean (both interface fields) |
| logs_sorted (4 conjuncts) | PROVED (base) | Raft/SortedInterface.v:9-35 | CreationRing.lean (logs_sorted_invariant) |
| votesWithLog_sorted | PROVED | Raft/VotesWithLogSortedInterface.v:9-12 | CreationRing.lean (invariant) |
| votesWithLog_term_sanity | PROVED | Raft/VotesWithLogTermSanityInterface.v:8-12 | CreationRing.lean (invariant) |
| current_term_gt_zero | PROVED (base) | Raft/CurrentTermGtZeroInterface.v:8-11 | CreationRing.lean (invariant) |
| terms_and_indices_from_one_log (+_nw) | PROVED (base) | Raft/TermsAndIndicesFromOneLogInterface.v:8-16 | CreationRing.lean (both fields) |
| terms_and_indices_from_one (vwl ∧ ll) | PROVED | Raft/TermsAndIndicesFromOneInterface.v:10-18 | CreationRing.lean (invariant) |
| leaderLogs_candidateEntries | PROVED | Raft/LeaderLogsCandidateEntriesInterface.v:9-13 | CreationRing.lean (invariant) |
| allEntries_votesWithLog (**GAP-7a**) | PROVED | Raft/AllEntriesVotesWithLogInterface.v:10-19 | LeaderLogsAssembly.lean (invariant) |
| leaderLogs_preserved (**GAP-7b**) | PROVED | Raft/LeaderLogsPreservedInterface.v:9-15 | LeaderLogsAssembly.lean (invariant) |
| append_entries_leaderLogs | PROVED | Raft/AppendEntriesRequestLeaderLogsInterface.v:12-22 | LeaderLogsAssembly.lean (invariant) |
| logs_leaderLogs (+ _nw) | PROVED | Raft/LogsLeaderLogsInterface.v:9-30 | LeaderLogsAssembly.lean (both invariants) |
| allEntries_leaderLogs_term | PROVED | Raft/AllEntriesLeaderLogsTermInterface.v:9-15 | LeaderLogsAssembly.lean (invariant) |
| allEntries_log | PROVED | Raft/AllEntriesLogInterface.v:10-19 | LeaderLogsAssembly.lean (invariant) |
| appendEntriesRequest_term_sanity | PROVED | Raft/AppendEntriesRequestTermSanityInterface.v:8-14 | LeaderCompleteness.lean:53 (invariant :63) |
| allEntries_candidateEntries | PROVED | Raft/AllEntriesCandidateEntriesInterface.v | LeaderCompleteness.lean:74 (invariant :85) |
| allEntries_leader_sublog | PROVED | Raft/AllEntriesLeaderSublogInterface.v:8-13 | LeaderCompleteness.lean:357 (invariant :453) |
| allEntries_log_matching | PROVED | Raft/AllEntriesLogMatchingInterface.v:8-14 | LeaderCompleteness.lean:902 (invariant :1418) |
| prefix_within_term (both fields) | PROVED | Raft/PrefixWithinTermInterface.v:21-28 | LeaderCompleteness.lean (allEntries_leaderLogs + log_log invariants; T2 nw fact + inductive) |
| leaderLogs_sorted (GAP-5a) | PROVED | Raft/LeaderLogsSortedInterface.v:9-13 | LogMatching.lean (invariant) |
| UniqueIndices (2 conjuncts) | PROVED (base) | Raft/UniqueIndicesInterface.v:9-20 | LogMatching.lean (UniqueIndices_invariant) |
| leader_sublog (2 conjuncts) | PROVED (base) | Raft/LeaderSublogInterface.v:8-27 | LogMatching.lean (leader_sublog_invariant_invariant) |
| **log_matching (LOG MATCHING, T3)** | PROVED (base) | Raft/LogMatchingInterface.v:9-65 | LogMatching.lean (log_matching_invariant + logMatchingStatement_holds) |
| leaderLogs_contiguous (GAP-5b) | PROVED | Raft/LeaderLogsContiguousInterface.v:9-12 | LogMatching.lean (invariant) |
| allEntries_indices_gt_0 | PROVED | Raft/AllEntriesIndicesGt0Interface.v:8-11 | LogMatching.lean (invariant) |
| refined_log_matching_lemmas (10 fields) | PROVED | Raft/RefinedLogMatchingLemmasInterface.v:9-113 | LogMatching.lean (ten standalone theorems, D3) |
| allEntries_term_sanity | PROVED | Raft/AllEntriesTermSanityInterface.v:8-12 | AppendEntriesChain.lean (invariant) |
| log_properties_hold_on_leader_logs | PROVED | Raft/LeaderLogsLogPropertiesInterface.v:9-17 | AppendEntriesChain.lean (invariant, higher-order) |
| leaders_have_leaderLogs_strong | PROVED | Raft/LeadersHaveLeaderLogsStrongInterface.v:8-16 | AppendEntriesChain.lean (invariant) |
| appendEntries_request_reply_correspondence | PROVED (base) | Raft/AppendEntriesRequestReplyCorrespondenceInterface.v:9-20 | AppendEntriesChain.lean (invariant + subset_reachable) |
| appendEntries_requests_came_from_leaders | PROVED | Raft/AppendEntriesRequestsCameFromLeadersInterface.v:8-15 | AppendEntriesChain.lean (invariant) |
| leaderLogs_sublog | PROVED | Raft/LeaderLogsSublogInterface.v:8-14 | AppendEntriesChain.lean (invariant) |
| appendEntries_leader | PROVED | Raft/AppendEntriesLeaderInterface.v:8-16 | AppendEntriesChain.lean (invariant; pre-state win_host route) |
| appendEntriesReply_sublog | PROVED (base) | Raft/AppendEntriesReplySublogInterface.v:8-16 | AppendEntriesChain.lean (invariant) |
| nextIndex_safety | PROVED (base) | Raft/NextIndexSafetyInterface.v:8-11 | AppendEntriesChain.lean (invariant) |
| leaderLogs_logMatching (leaderLogs_entries_match) | PROVED | Raft/LeaderLogsLogMatchingInterface.v:9-13 | AppendEntriesChain.lean (conj invariant + interface half) |
| msg_refined_raft_net_invariant (msg-ghost principle, GAP-2) | PROVED (unprimed + simulation_1/lift/deghost_spec + witness; primed set + reghosting deferred, census logged) | Raft/RaftMsgRefinementInterface.v:34-195 + RaftProofs/RaftMsgRefinementProof.v:12-275,566-654 | MsgRefinement.lean |
| transitive_commit | PROVED | Raft/TransitiveCommitInterface.v:9-15 | SafetyLeaves.lean (invariant) |
| all_entries_leader_logs (4 conjuncts) | PROVED | Raft/AllEntriesLeaderLogsInterface.v | SafetyLeaves.lean (assembly over ported invariants) |
| in_log_in_all_entries | PROVED | Raft/InLogInAllEntriesInterface.v | SafetyLeaves.lean (invariant) |
| log_all_entries | PROVED | Raft/LogAllEntriesInterface.v | SafetyLeaves.lean (invariant) |
| lastApplied_le_commitIndex | PROVED (base) | Raft/LastAppliedLeCommitIndexInterface.v | SafetyLeaves.lean (invariant) |
| no_append_entries_to_self | PROVED (base) | Raft/NoAppendEntriesToSelfInterface.v | SafetyLeaves.lean (invariant) |
| match_index_sanity | UNIT-13 CHARTER (W-B remainder) | Raft/MatchIndexSanityInterface.v | — |
| prevLog_candidateEntriesTerm | UNIT-13 CHARTER (W-B remainder) | Raft/PrevLogCandidateEntriesTermInterface.v | — |
- 2026-08-22 Slice 13 (1cc83c1d): log/message spec lemmas for the ring
  (findGtIndex_in, removeAfterIndex_in, per-handler log facts,
  doLeader_messages, rvr cronies function-level cases).
- 2026-08-22 Slice 14: `CandidateEntries.lean` opened —
  `cronies_term_invariant` (CroniesTermProof.v:271-291 shape, ghost)
  and `no_entries_past_current_term_invariant`
  (TermSanityProof.v:373-395, BASE — second real instantiation of the
  base principle; the nw conjunct's do_leader case rides
  doLeader_messages + the host invariant, exactly upstream's
  findGtIndex argument). INDEX updates: cronies_term PROVED
  (CandidateEntries.lean:43), no_entries_past_current_term PROVED
  (CandidateEntries.lean, term-sanity section); mem_of_mem_remove_middle
  un-privated (2nd consumer). Build green.
- 2026-08-22 Slice 15 (66710572): `candidateEntries` + the per-handler
  preserves lemmas + `candidate_entries_invariant`. [AGENT] proof-shape
  notes: (a) the timeout case uses `cronies_term` exactly as upstream —
  a winner at the fresh term (old+1) would put a crony past the old
  current term; (b) the RVR case is the one that leans on
  `cronies_correct` (a standing leader's votesReceived won —
  RefinementCommonTheorems.v:138's cci dependency); (c) `rcases h : x
  with ...` substitution BREAKS goals mentioning the scrutinee — the
  by_cases + `serverType_cases` helper pattern replaces it (recorded
  for successors). Three AxCheck pins added (sweep 1244).
- 2026-08-22 CHECKPOINT (recomputed from artifacts per coordinator
  item 4, at 66710572): `git log f64d9b21..HEAD | wc -l` = 20 commits;
  capped `lake build` green with `AxCheck sweep: 1244 declarations ...
  within [propext, Quot.sound]`; diffharness fixture pin OK (320
  cases); `grep -rc sorry|native_decide` over compat/verdi/VerdiCompat:
  single hit = Examples.lean:12, prose in a P1-era docstring
  (pre-campaign file, commit 6fb4caf1), zero in campaign files;
  CandidateEntries.lean = 1199 lines (wc). Unit-3 remaining:
  scripts/ci + final entry.
- 2026-08-22 Unit-3 final gate: `GOLEAN_ALLOW_NO_DIFF=1
  GOLEAN_MEM_MAX=24G scripts/ci` — **RESULT: PASS, exit 0** (log:
  `artifacts/ci-arc3-unit3.log`, gitignored; no-diff notes are the
  allowed docs+compat hatch — unit 3 touched only `compat/verdi/**` +
  this log). Comparator-landmark staleness note still report-only;
  flagged for the operator's merge step as before.

## Final entry — unit 3 complete (2026-08-22, tip = this commit)

**Proved at tip** — the candidate_entries ring, statements 1:1 with
their Interface files, zero sorry/native_decide in campaign files
(grep; sweep-enforced). `#print axioms` verbatim (fresh
`lake env lean` run):

```
'VerdiCompat.Raft.cronies_term_invariant' depends on axioms: [propext, Quot.sound]
'VerdiCompat.Raft.no_entries_past_current_term_invariant' depends on axioms: [propext, Quot.sound]
'VerdiCompat.Raft.candidate_entries_invariant' depends on axioms: [propext, Quot.sound]
```

Inventory: `CandidateEntries.lean` (1199 lines): `cronies_term` (:37,
invariant :43), `no_entries_past_current_term` (:214, invariant :220,
BASE), `candidateEntries`/`CandidateEntries` (:596) with per-handler
preserves lemmas, `candidate_entries_invariant` (:808). Spec-lemma
additions in ElectionSpecLemmas.lean (slice 13 + timeout/rvr
function-level cronies cases). The INVARIANT INDEX above is current.

**Coordinator items resolved:** (1) unit-2 re-verification recorded at
unit start; (2) INVARIANT INDEX opened and kept current (10 rows, all
build-verified); (3) GAP-2 (msg-ghost) was NOT needed by this ring —
still open, untouched; (4) checkpoint recomputed from artifacts at
66710572.

**Honestly open:** GAP-1 (primed variants — still never triggered),
GAP-2 (msg-ghost layer), GAP-4 (classical-list doctrine question) all
carried unchanged.

**Next unit's charter (Arc 3, unit 4 — proposal):** continue the
leader-completeness lattice per the index: the `leaderLogs` ring —
`leaderLogs_term_sanity` (LeaderLogsTermSanityInterface.v),
`leaderLogs_sorted`/`_contiguous`, then `leaders_have_leaderLogs`
(LeadersHaveLeaderLogsInterface.v) and `one_leaderLog_per_term`
(OneLeaderLogPerTermInterface.v) — the ghost `leaderLogs` vocabulary
candidate_entries' successors consume, converging on
`leader_completeness`. Same conventions; msg-ghost (GAP-2) expected to
stay untouched until the GhostLog* files.

## Unit 4 — the leaderLogs ring (2026-08-22, coordinator-accepted charter)

Scope per the coordinator's charter: `leaderLogs_term_sanity` →
`leaders_have_leaderLogs` → `one_leaderLog_per_term`, converging on the
`leader_completeness` STATEMENT (defs 1:1; its proof is a later arc's).
Same conventions; GAP-2 msg-ghost only on first genuine need.

- 2026-08-22 SUCCESSOR RE-VERIFICATION of unit 3 (recomputed, fresh
  reader): fresh capped `lake build` at d07c5382 — green ("Build
  completed successfully (58 jobs)"; fully cached, so the sweep line was
  re-derived by a fresh capped `lake env lean AxCheck.lean`, which
  printed verbatim `AxCheck sweep: 1244 declarations across VerdiCompat
  modules, axiom set within [propext, Quot.sound]`); fresh
  `#print axioms` (capped `lake env lean` probe):
  `candidate_entries_invariant`, `one_leader_per_term_invariant`,
  `lower_prop` all `[propext, Quot.sound]`; hatch grep
  (`sorry|native_decide|^axiom| axiom `) over RefinedProofStructure/
  ElectionSafety/CandidateEntries/ElectionSpecLemmas: 3 hits, all
  docstring prose (RefinedProofStructure.lean:744,
  ElectionSafety.lean:1521, :1581 — the axiom-set commentary). All
  claims hold; building on them.
- 2026-08-22 [AGENT] Unit-4 scope call, from the full upstream
  dependency map (read at `deps/verdi-raft` @ a3375e8, pin re-verified
  by `git rev-parse`): upstream's `one_leaderLog_per_term` proof
  (OneLeaderLogPerTermProof.v:1-258) requires a closure the charter
  does not name — `leaderLogs_votesWithLog` (its RVR contradiction
  case), which pulls `votesReceived_moreUpToDate` +
  `requestVoteReply_moreUpToDate`, which pull
  `requestVote_maxIndex_maxTerm` + `requestVoteReply_term_sanity` +
  `votedFor_moreUpToDate`, which pull `requestVote_term_sanity` +
  `votedFor_term_sanity`; plus `votes_votesWithLog_correspond`, and
  (for leaderLogs_term_sanity) base `candidate_term_gt_log` lifted via
  `lift_prop` — first real `lift_prop` consumer. DECISION: port the
  whole closure 1:1 rather than invent a shortcut route (the
  moreUpToDate/votesWithLog cluster is exactly the votes-with-log side
  the leader-completeness lattice consumes next — not throwaway; a
  bespoke shorter argument would diverge from the ~73-file chain
  architecture Plan A is porting). `leaderLogs_sorted`/`_contiguous`
  (named in the predecessor's proposal, not in the operative charter)
  are NOT consumed by this ring — deferred to first need, recorded
  as in-scope-later, not a gap.
- 2026-08-22 [AGENT] File plan: one new file `LeaderLogs.lean`
  (importing CandidateEntries) for the whole ring + closure;
  leaderLogs/votesWithLog ghost-update lemmas added to
  ElectionSpecLemmas.lean beside their votes/cronies siblings.
- 2026-08-22 Slice 17 (b10e2cee): unit-4 spec lemmas —
  handleTimeout_messages, handleRequestVote reply-term/grant (the
  moreUpToDate guard surfaced), handleRequestVoteReply
  leader-transition (SpecLemmas.v:467's spec'), leaderLogs ghost
  elim/old/intro for RVR + timeout-unchanged, votesWithLog
  old/cases/votedFor-cases (RefinementSpecLemmas.v:599-660), and the
  votes/votesWithLog lockstep shapes. Build green.
- 2026-08-22 Slice 18: `LeaderLogs.lean` opened — the ring's leaves:
  `requestVote_term_sanity` (nw), `votes_votesWithLog_correspond`
  (via a net'-generic step helper mirroring
  VotesVotesWithLogCorrespondProof.v:12-36), and
  `leaders_have_leaderLogs` (rri-only; the RVR case splits standing
  leader / fresh winner on handleRequestVoteReply_spec's leader
  clause, the winner witnessed by the new leaderLogs snapshot). Wired
  into VerdiCompat.lean (sweep covers it from birth: 1300 decls,
  within [propext, Quot.sound]). [AGENT] Gotcha recorded for
  successors: `==` on Nat here is `instBEqOfDecidableEq`, and BOTH
  `simp [moreUpToDate]` and `beq_self_eq_true` drag `Classical.choice`
  through its LawfulBEq instance — the enforcing sweep caught it
  twice; the clean form is `decide_eq_true (Eq.refl _)` (this is the
  same gate-catch class as unit 3's eraseOne, recorded not worked
  around). Also: `nomatch h` inside an anonymous-constructor pair
  swallows the following comma — parenthesize.
- 2026-08-22 Slice 19: the tier-B term-sanity trio —
  `votedFor_term_sanity` (via a promoted step helper
  `votedFor_term_sanity_of_update`: term-growth + vote-preserved-or-
  directly-bounded, collapsing upstream's eleven near-identical Ltac
  cases; the requestVote case consumes `requestVote_term_sanity` on the
  in-flight request, exactly VotedForTermSanityProof.v:56-69),
  `requestVoteReply_term_sanity` (the request_vote case rides
  `handleRequestVote_grant`: a grant is issued at exactly the request's
  term) and `requestVote_maxIndex_maxTerm` (the timeout case's stale-
  packet contradiction via requestVote_term_sanity, upstream's rvtsi
  argument). Plus `handleClientRequest_not_leader` in the spec lemmas.
  [AGENT] Gotcha for successors: `subst heq` with `heq : h0 = h`
  (var = var) eliminates the RIGHT variable, but with
  `heq : h0 = p.pDst` (var = projection) eliminates the LEFT — the
  surviving name differs by case; reference accordingly. Build green.
- 2026-08-22 Slice 20: `candidate_term_gt_log` (BASE — third real base
  instantiation; timeout case rides no_entries_past_current_term
  exactly as upstream's tsi) and the `leaderLogs_term_sanity` TRIO
  (LeaderLogsTermSanityInterface.v:9-24 1:1) — each with its
  `_of_update` step helper mirroring upstream's `*_unchanged` lemmas;
  the term-sanity RVR case is the FIRST REAL `lift_prop` CONSUMER
  (lifting base candidate_term_gt_log into the ghost proof, exactly
  LeaderLogsTermSanityProof.v:17-23's candidate_term_gt_log_lifted);
  the candidate variant's timeout case rides invariant 2, upstream's
  `intuition auto with arith`. Full build green, sweep 1350 decls
  within [propext, Quot.sound].
- 2026-08-22 CHECKPOINT (recomputed at this tip, 5 slices since the
  unit-3 checkpoint): `git log f64d9b21..HEAD --oneline | wc -l` = 26
  commits including the slice-20 commit; capped full `lake build`
  green, `AxCheck sweep: 1350 declarations ... within
  [propext, Quot.sound]`;
  `grep -n sorry\|native_decide` over LeaderLogs.lean: 0 hits;
  LeaderLogs.lean = 2040 lines (wc). Ring state: requestVote/votedFor/
  requestVoteReply term sanity ✓, requestVote_maxIndex_maxTerm ✓,
  votes_votesWithLog_correspond ✓, leaders_have_leaderLogs ✓,
  candidate_term_gt_log (base) ✓, leaderLogs_term_sanity trio ✓.
  Remaining: votedFor/requestVoteReply/votesReceived moreUpToDate,
  leaderLogs_votesWithLog, one_leaderLog_per_term (3 statements),
  leader_completeness defs, pins, INDEX, gate.
- 2026-08-22 Slice 21: `votedFor_moreUpToDate`
  (VotedForMoreUpToDateInterface.v:8-18 1:1) — the votesWithLog chain's
  first moreUpToDate invariant. A candidate-freezing step helper
  (`votedFor_moreUpToDate_of_update`) covers seven handlers; timeout
  (self-vote-with-log witness + the votedFor_term_sanity stale-vote
  contradiction, upstream's vftsi) and request_vote (fresh-grant record
  as witness; self-grant closed by moreUpToDate_refl; cross-grant by
  requestVote_maxIndex_maxTerm, upstream's rvmimti) are manual.
  [AGENT] omega gotcha recorded: omega reports "no usable constraints"
  on hypotheses typed through the `term` abbrev in this context —
  `Nat.not_succ_le_self`/`Nat.ne_of_lt` close the same goals; earlier
  units' omega uses were over plain Nat. Build green.
- 2026-08-22 Slice 22: `requestVoteReply_moreUpToDate` (the request_vote
  case splits on the emitted grant — standing-vote via
  votedFor_moreUpToDate (upstream's vfmutdi), fresh-record via
  requestVote_maxIndex_maxTerm; the timeout case's stale-grant
  contradiction via requestVoteReply_term_sanity, upstream's rvrtsi)
  and `votesReceived_moreUpToDate` (the RVR case's fresh supporter
  rides the consumed grant packet through
  requestVoteReply_moreUpToDate — upstream's rvrmutdi — and the
  timeout candidacy's only supporter is the recorded self-vote). Both
  with candidate-freezing step helpers. Build green.
- 2026-08-22 Slice 23: `leaderLogs_votesWithLog`
  (LeaderLogsVotesWithLogInterface.v:10-18 1:1) — every leaderLog backed
  by a moreUpToDate quorum of recorded votes-with-log. `quorum_preserved`
  + an unchanged-step helper cover ten obligations; the RVR win case
  builds the quorum as `dedup (src :: votesReceived)` (upstream's
  wonElection_dedup_spec route): the replier via
  requestVoteReply_moreUpToDate on the consumed grant, the tallied via
  votesReceived_moreUpToDate, glued by
  handleRequestVoteReply_leader_transition. Build green.
- 2026-08-22 Slice 24: **`one_leaderLog_per_term`** — the ring's exit
  theorem (OneLeaderLogPerTermInterface.v:8-44, all three statements
  1:1; the two convenience variants as projections of the main
  invariant). The RVR case's fresh-win cross-host contradiction is
  `one_leaderLog_win_host` (upstream's contradiction_case,
  OneLeaderLogPerTermProof.v:140-177): the standing leaderLog's quorum
  (leaderLogs_votesWithLog) and the win's tally share a voter (pigeon
  over nodes, unit-3's constructive counting layer), who voted once per
  term (votes_correct) — so the hosts coincide; the old-beside-fresh
  same-host case dies on leaderLogs_currentTerm_sanity_candidate. Plus
  the `leader_completeness` STATEMENT defs
  (LeaderCompletenessInterface.v:9-42 1:1 — directly_committed,
  committed, both lc conjuncts; defs only, the proof is a later unit's,
  per the charter's "converging on the statement").
- 2026-08-22 Slice 25: AxCheck curated pins for the six unit-4
  headliners (candidate_term_gt_log / leaderLogs_term_sanity /
  leaders_have_leaderLogs / votedFor_moreUpToDate /
  leaderLogs_votesWithLog / one_leaderLog_per_term invariants),
  captured from a fresh `#print axioms` run — all
  [propext, Quot.sound]; the full 15-theorem probe of the unit
  likewise all [propext, Quot.sound]. Full build green: AxCheck sweep
  1403 decls; grep sorry/native_decide over LeaderLogs.lean: 0;
  LeaderLogs.lean = 3908 lines (wc). INVARIANT INDEX extended by the
  unit's 13 rows (build-verified at this tip).
- 2026-08-22 Unit-4 final gate: `GOLEAN_ALLOW_NO_DIFF=1
  GOLEAN_MEM_MAX=24G scripts/ci` — **RESULT: PASS, exit 0** (log:
  `artifacts/ci-arc3-unit4.log`, gitignored; the no-diff notes are the
  allowed docs+compat hatch — unit 4 touched only `compat/verdi/**` +
  this log). The report-only comparator-landmark note now reads
  "56 theorems @ 1730567a2d3f, 35 commit(s) ago" — same
  operator-merge-time flag as units 1-3; nothing in this unit touches a
  designated statement or Challenge's closure (statement-TCB step ok).

## Final entry — unit 4 complete (2026-08-22, tip = this commit)

**Proved at tip** — the leaderLogs ring, statements 1:1 with their
Interface files @ a3375e8, proofs re-derived through the ported
principles; zero sorry/native_decide in campaign files (grep;
sweep-enforced: 1403 declarations within [propext, Quot.sound], plus
six new curated pins). `#print axioms` verbatim (fresh capped
`lake env lean` probe against the built package):

```
'VerdiCompat.Raft.candidate_term_gt_log_invariant' depends on axioms: [propext, Quot.sound]
'VerdiCompat.Raft.leaderLogs_term_sanity_invariant' depends on axioms: [propext, Quot.sound]
'VerdiCompat.Raft.leaders_have_leaderLogs_invariant' depends on axioms: [propext, Quot.sound]
'VerdiCompat.Raft.leaderLogs_votesWithLog_invariant' depends on axioms: [propext, Quot.sound]
'VerdiCompat.Raft.one_leaderLog_per_term_invariant' depends on axioms: [propext, Quot.sound]
'VerdiCompat.Raft.votedFor_moreUpToDate_invariant' depends on axioms: [propext, Quot.sound]
'VerdiCompat.Raft.votes_votesWithLog_correspond_invariant' depends on axioms: [propext, Quot.sound]
'VerdiCompat.Raft.requestVoteReply_moreUpToDate_invariant' depends on axioms: [propext, Quot.sound]
'VerdiCompat.Raft.votesReceived_moreUpToDate_invariant' depends on axioms: [propext, Quot.sound]
'VerdiCompat.Raft.requestVote_term_sanity_invariant' depends on axioms: [propext, Quot.sound]
'VerdiCompat.Raft.votedFor_term_sanity_invariant' depends on axioms: [propext, Quot.sound]
'VerdiCompat.Raft.requestVoteReply_term_sanity_invariant' depends on axioms: [propext, Quot.sound]
'VerdiCompat.Raft.requestVote_maxIndex_maxTerm_invariant' depends on axioms: [propext, Quot.sound]
'VerdiCompat.Raft.leaderLogs_currentTerm_sanity_invariant' depends on axioms: [propext, Quot.sound]
'VerdiCompat.Raft.leaderLogs_currentTerm_sanity_candidate_invariant' depends on axioms: [propext, Quot.sound]
```

Inventory: `LeaderLogs.lean` (3908 lines) — the charter's named chain
`leaderLogs_term_sanity` (trio) → `leaders_have_leaderLogs` →
**`one_leaderLog_per_term`** (+ `_log`/`_host`), converging on the
**`leader_completeness` STATEMENT** (defs 1:1); plus the closure the
charter's chain forced (logged scope call at unit start):
`requestVote/votedFor/requestVoteReply_term_sanity`,
`requestVote_maxIndex_maxTerm`, `votes_votesWithLog_correspond`,
`candidate_term_gt_log` (BASE), and the moreUpToDate cluster
(`votedFor/requestVoteReply/votesReceived_moreUpToDate`,
`leaderLogs_votesWithLog`) — the votes-with-log side the
leader-completeness lattice consumes next. The INVARIANT INDEX above
is current (23 rows). First real `lift_prop` consumer landed
(leaderLogs_term_sanity's RVR case lifting base
candidate_term_gt_log).

**Honestly open (carried + new):**
- GAP-1 (primed variants): STILL never triggered — no unit-4 proof
  needed one; carried.
- GAP-2 (msg-ghost layer): NOT needed by this ring (as predicted —
  everything here is plain rri); carried untouched.
- GAP-4 (classical-list doctrine): carried; unit 4 hit the same class
  twice more (instBEqOfDecidableEq's LawfulBEq, the `term`-abbrev
  omega failure) and resolved constructively both times.
- GAP-5 (new): `leaderLogs_sorted`/`_contiguous`
  (LeaderLogsSorted/ContiguousInterface.v) were named in the
  predecessor's proposal but are NOT consumed by this ring and not in
  the operative charter — deferred to first need (they feed the
  log-matching side).
- GAP-6 (new): `leader_completeness` is a STATEMENT port only; its
  proof (LeaderCompletenessProof.v, 379 lines) additionally needs
  PrefixWithinTerm, LeaderLogsPreserved, EveryEntryWasCreated,
  AllEntriesVotesWithLog, VotesWithLogSorted, TermsAndIndicesFromOne,
  LeaderLogsLogMatching (imports read at a3375e8) — the next two
  units' lattice.

**Next unit's charter (Arc 3, unit 5 — proposal):** the creation ring
feeding leader_completeness, per LeaderCompletenessProof.v's import
closure: `every_entry_was_created` (EveryEntryWasCreatedInterface.v) →
`allEntries_votesWithLog` (AllEntriesVotesWithLogInterface.v) →
`votesWithLog_sorted` (VotesWithLogSortedInterface.v) →
`terms_and_indices_from_one` (TermsAndIndicesFromOneInterface.v) →
`leaderLogs_preserved` (LeaderLogsPreservedInterface.v), leaving the
log-matching heavies (PrefixWithinTerm, LeaderLogsLogMatching — which
will also consume GAP-5's sorted/contiguous) for unit 6 and
`leader_completeness`'s proof for unit 7. Same conventions; successors
re-verify this unit's claims fresh (build + sweep count 1403 + the
probe above + hatch grep over LeaderLogs.lean).

## Unit 5 — the creation ring (2026-08-22, coordinator-accepted charter)

Coordinator additions folded in: GAP-2 minimal-port-on-first-need if
the ring touches the msg-ghost layer; INTEGRATION READINESS note in the
unit report (lane 29+ commits deep).

- 2026-08-22 SUCCESSOR-STYLE RE-VERIFICATION of unit 4 (recomputed):
  fresh capped `lake env lean AxCheck.lean` printed verbatim `AxCheck
  sweep: 1403 declarations across VerdiCompat modules, axiom set within
  [propext, Quot.sound]`; fresh `#print axioms` probe:
  `one_leaderLog_per_term_invariant` + the term-sanity trio all
  `[propext, Quot.sound]`; `grep -c "sorry\|native_decide"` over
  LeaderLogs.lean: 0. Claims hold; building on them.
- 2026-08-22 [AGENT] Unit-5 scope call, from the actual import closure
  (read at a3375e8 — my unit-4 proposal was drafted from
  LeaderCompletenessProof.v's FIRST-level imports only; the
  second-level ground truth narrows it): (a) NO msg-ghost anywhere in
  the ring — GAP-2 stays untouched, as chartered "on first need" with
  no need arising; (b) `allEntries_votesWithLog` requires
  `AllEntriesLog` (AllEntriesLogProof.v, 1089 lines, itself importing
  AppendEntriesRequestLeaderLogs, RefinedLogMatchingLemmas,
  AllEntriesLeaderLogsTerm, LeaderLogsContiguous, LeaderLogsSorted,
  AllEntriesTermSanity) and `leaderLogs_preserved` requires
  `LogsLeaderLogs` (848 lines, importing LeaderLogsSorted/Contiguous/
  LogMatching, RefinedLogMatchingLemmas, LeadersHaveLeaderLogsStrong,
  NextIndexSafety, LeaderLogsLogProperties) — BOTH sit on exactly the
  log-matching subtree the charter defers to unit 6. DECISION: port
  the feasible creation ring now — `every_entry_was_created` (deps:
  leaders_have_leaderLogs ✓), base `logs_sorted` (SortedInterface.v,
  4 conjuncts; dep: term_sanity ✓) → `votesWithLog_sorted`,
  `current_term_gt_zero` → `terms_and_indices_from_one_log` (base) →
  `terms_and_indices_from_one`, `votesWithLog_term_sanity` (94-line
  feeder of allEntries_votesWithLog), and `leaderLogs_candidate_entries`
  (LeaderLogsCandidateEntriesProof.v, 287 lines — ALL its deps are
  already proved: CandidateEntries/CroniesCorrect/CroniesTerm/
  LeaderLogsTermSanity ✓; it is leaderLogs_preserved's other input);
  record `allEntries_votesWithLog` + `leaderLogs_preserved` as GAP-7
  (blocked on the unit-6 log-matching subtree), not silently attempted.
- 2026-08-22 [AGENT] File plan: new `CreationRing.lean` (imports
  LeaderLogs); `term_was_created`/`in_any_log`
  (RefinementCommonDefinitions.v:20-23 / EveryEntryWasCreatedInterface.v
  1:1) live there with citations.
- 2026-08-22 Slice 26: `CreationRing.lean` opened —
  **`every_entry_was_created`** via the `in_any_log` strengthening
  (EveryEntryWasCreatedProof.v's route 1:1: the ONLY entry-creation
  step is a leader's client request, certified by
  leaders_have_leaderLogs; every other handler traces entries back —
  accepted appends to the in-flight packet, doLeader messages to the
  sender's log, the RVR win snapshot to the winner's unchanged log —
  and leaderLogs only grow, `term_was_created_of_update`). Both
  interface fields delivered. Wired into VerdiCompat.lean.
- 2026-08-22 Slice 27: the BASE `logs_sorted` conjunction
  (SortedInterface.v:9-35 1:1, four conjuncts; fourth real base
  instantiation) + the constructive sorted machinery
  (sorted_append/sorted_index_term/removeAfterIndex_sorted/_In_le/
  maxIndex_is_max/findGtIndex_necessary/sorted_findGtIndex/
  findAtIndex_elim — CommonTheorems.v slices, direct inductions in
  place of upstream's subseq route) + `handleAppendEntries_log_cases`
  (SpecLemmas.v:149-175's detailed shape) and
  `doLeader_messages_sorted` (SortedProof.v:441-466). The accept-splice
  case is upstream's sorted_append argument verbatim
  (SortedProof.v:276-309); client_request rides
  no_entries_past_current_term exactly as upstream's tsi. Build green.
- 2026-08-22 Slice 28: `votesWithLog_sorted` +
  `votesWithLog_term_sanity` proved TOGETHER (their per-handler elim
  facts are identical — one derivation, consumed twice, via
  `votesWithLog_facts_of_update`); the fresh-record cases ride
  `sorted_host_lifted` (VotesWithLogSortedProof.v:45-55 — second real
  `lift_prop` consumer, lifting base logs_sorted). New elim lemmas:
  requestVote/timeout votesWithLog full elims (record = responder's new
  term + unchanged log).
- 2026-08-22 Slice 29: `current_term_gt_zero` (BASE — a non-follower's
  term passed a candidacy's +1; a strictly-grown term is ≥ 1 outright)
  + `terms_and_indices_from_one_log`/`_nw` (BASE, both fields together;
  the creation step's entry is at the leader's ≥ 1 term and a fresh
  ≥ 1 index — `handleClientRequest_log_index` added) +
  `terms_and_indices_from_one` (ghost vwl ∧ ll; `tai_log_lifted` is the
  third `lift_prop` consumer; the vwl/ll fresh records are nodes' own
  bounded logs).
- 2026-08-22 Slice 30: `leaderLogs_candidateEntries`
  (LeaderLogsCandidateEntriesInterface.v:9-13 1:1) — every leaderLog
  entry is a candidate entry. Unit 3's per-handler
  `*_preserves_candidateEntries` transport lemmas carry the witness
  through every step (the promotion-ledger payoff: five lemmas, six new
  consumers); the RVR fresh-snapshot case is
  `candidate_entries_invariant`'s host part on the winner's unchanged
  log, exactly LeaderLogsCandidateEntriesProof.v:166-183.
- 2026-08-22 CHECKPOINT (recomputed at this tip; the unit-4 final entry
  at slice 25 served as the last full recompute): `git log
  f64d9b21..HEAD --oneline | wc -l` = 34 commits; capped full
  `lake build` green with `AxCheck sweep: 1528 declarations ... within
  [propext, Quot.sound]` (five new curated pins for the unit-5
  headliners, captured from a fresh probe); grep sorry/native_decide
  over CreationRing.lean: 0; CreationRing.lean = 2511 lines,
  LeaderLogs.lean = 3908 (wc). Unit-5 remaining: INDEX rows, gate,
  final entry + INTEGRATION READINESS note.
- 2026-08-22 [AGENT] Housekeeping fix rode this unit: compat/verdi's
  lakefile.toml comment still described AxCheck as "advisory" — stale
  since the 2026-08-10 enforcing upgrade (AxCheck.lean's own header and
  the throwError sweep are the ground truth). Comment corrected, no
  behavior change.
- 2026-08-22 Unit-5 final gate: `GOLEAN_ALLOW_NO_DIFF=1
  GOLEAN_MEM_MAX=24G scripts/ci` — **RESULT: PASS, exit 0** (log:
  `artifacts/ci-arc3-unit5.log`, gitignored; no-diff notes are the
  allowed docs+compat hatch — unit 5 touched only `compat/verdi/**` +
  this log). Comparator-landmark staleness note remains report-only —
  same operator-merge-time flag as units 1-4.

## Final entry — unit 5 complete (2026-08-22, tip = this commit)

**Proved at tip** — the creation ring's feasible slice, statements 1:1
with their Interface files @ a3375e8; zero sorry/native_decide in
campaign files (grep; sweep-enforced: 1528 declarations within
[propext, Quot.sound], plus five new curated pins). `#print axioms`
verbatim (fresh capped `lake env lean` probe):

```
'VerdiCompat.Raft.every_entry_was_created_invariant' depends on axioms: [propext, Quot.sound]
'VerdiCompat.Raft.every_entry_was_created_in_any_log_invariant' depends on axioms: [propext, Quot.sound]
'VerdiCompat.Raft.logs_sorted_invariant' depends on axioms: [propext, Quot.sound]
'VerdiCompat.Raft.votesWithLog_sorted_invariant' depends on axioms: [propext, Quot.sound]
'VerdiCompat.Raft.votesWithLog_term_sanity_invariant' depends on axioms: [propext, Quot.sound]
'VerdiCompat.Raft.current_term_gt_zero_invariant' depends on axioms: [propext, Quot.sound]
'VerdiCompat.Raft.terms_and_indices_from_one_log_and_nw_invariant' depends on axioms: [propext, Quot.sound]
'VerdiCompat.Raft.terms_and_indices_from_one_invariant' depends on axioms: [propext, Quot.sound]
'VerdiCompat.Raft.leaderLogs_candidateEntries_invariant' depends on axioms: [propext, Quot.sound]
```

Inventory: `CreationRing.lean` (2511 lines) — `every_entry_was_created`
(both interface fields, via the `in_any_log` strengthening), base
`logs_sorted` (4 conjuncts) with the constructive sorted machinery,
`votesWithLog_sorted` + `votesWithLog_term_sanity` (shared derivation),
base `current_term_gt_zero` and `terms_and_indices_from_one_log`/`_nw`,
ghost `terms_and_indices_from_one` (vwl ∧ ll), and
`leaderLogs_candidateEntries` (unit 3's transport lemmas re-consumed).
Three new `lift_prop` consumers (sorted_host_lifted, tai_log_lifted,
plus unit 4's candidate_term_gt_log lift). The INVARIANT INDEX above is
current (34 rows incl. the two GAP-7 rows).

**Honestly open (carried + new):**
- GAP-1 (primed variants): STILL never triggered; carried.
- GAP-2 (msg-ghost): NOT touched — the creation ring is plain rri
  (verified against every proof file's imports at unit start); the
  coordinator's minimal-port-on-first-need clause was never invoked.
- GAP-4/GAP-5/GAP-6: carried unchanged.
- GAP-7 (recorded at unit start, scope call): `allEntries_votesWithLog`
  (needs AllEntriesLog, 1089 lines + its 6-interface subtree) and
  `leaderLogs_preserved` (needs LogsLeaderLogs, 848 lines + its
  7-interface subtree) — both sit on the unit-6 log-matching heavies;
  deferred with the evidence, not attempted.

**INTEGRATION READINESS (coordinator-requested):** compat/verdi is a
SELF-CONTAINED lake package — zero external lake dependencies
(lake-manifest packages: []), pinned toolchain `leanprover/lean4:v4.31.0`,
default targets = VerdiCompat + AxCheck (enforcing) + diffharness. A
fresh checkout of `campaign-arc3` builds it standalone with
`cd compat/verdi && <capped> lake build` — no `deps/` checkout needed
(the verdi/verdi-raft trees are reference-reading only; all reads went
through the MAIN checkout's pins, verified each unit). The lane touched
ONLY `compat/verdi/**` + `docs/campaign-arc3*` — no runtime code, no
`Corpus/`, no `baselines/` — so the eventual merge has no textual or
semantic overlap with the semantic core and no baseline re-pin;
`scripts/ci` on a fresh worktree needs `GOLEAN_ALLOW_NO_DIFF=1` until a
differential is recorded (standing docs+compat-lane hatch). Ordering
constraints: none within the repo; the single operator obligation at
merge time is the standing comparator-landmark staleness note
(report-only in ci; the widened trigger makes the judge run a
MERGE-STEP obligation, flagged in every unit's gate entry). File-add
order inside the lane is linear (ElectionSpecLemmas → ElectionSafety →
CandidateEntries → LeaderLogs → CreationRing, each imported by its
successor + all wired into VerdiCompat.lean), so cherry-picking partial
units would break imports — merge the branch tip, not slices.

**Next unit's charter (Arc 3, unit 6 — proposal):** the log-matching
subtree, in dependency order from the leaves:
`leaderLogs_sorted`/`leaderLogs_contiguous` (GAP-5; deps: sorted ✓ +
contiguity vocabulary) → `allEntries_term_sanity` +
`allEntries_leaderLogs_term` → `appendEntries_request_leaderLogs` →
`refined_log_matching_lemmas` (the base log-matching bridge — check
whether base `log_matching` itself must port first) →
`AllEntriesLog` → `allEntries_votesWithLog` (GAP-7a), and
`leadersHaveLeaderLogs_strong` + `nextIndex_safety` +
`leaderLogs_logProperties` → `LogsLeaderLogs` → `leaderLogs_preserved`
(GAP-7b) — then unit 7: `prefix_within_term` + `leaderLogs_logMatching`
→ `leader_completeness`'s PROOF (GAP-6). The successor should re-derive
this order from the import closure before starting (my unit-5 lesson:
first-level imports understate the tree).

## Unit 6 — the log-matching core (2026-08-22, coordinator-accepted charter)

Charter: the log-matching subtree, leaves-first, toward GAP-7a
(`allEntries_votesWithLog` via AllEntriesLog) and GAP-7b
(`leaderLogs_preserved` via LogsLeaderLogs). FIRST ACTION per the
charter + the unit-5 lesson: the full import closure of both targets
derived fresh before any proving; if it exceeds one unit, scope to the
largest self-contained prefix and record the remainder as the unit-7
charter.

- 2026-08-22 SUCCESSOR RE-VERIFICATION of unit 5 (recomputed, fresh
  reader): tip `2d93b2f04ea55d968c24ca2a7c5b791fd50c7fb2`, tree clean.
  Fresh capped `lake build` (24G) green ("Build completed successfully
  (41 jobs)"); the sweep line in that build was a cache replay, so
  re-derived by a fresh capped `lake env lean AxCheck.lean`, which
  printed verbatim `AxCheck sweep: 1528 declarations across VerdiCompat
  modules, axiom set within [propext, Quot.sound]`. Fresh
  `#print axioms` probe (capped `lake env lean`, repo-local scratch
  file — /tmp is write-only under this sandbox profile):
  `every_entry_was_created_invariant`, `one_leaderLog_per_term_invariant`,
  `logs_sorted_invariant` all
  `depends on axioms: [propext, Quot.sound]` verbatim. Hatch grep
  (`sorry|native_decide|^axiom| axiom `) over the six campaign files:
  4 hits, all docstring prose (RefinedProofStructure.lean:744,
  ElectionSpecLemmas.lean:953, ElectionSafety.lean:1521, :1581). All
  claims hold; building on them.
- 2026-08-22 [AGENT] FULL IMPORT CLOSURE of the two GAP-7 targets,
  derived by a transitive walk of `Require Import/Export` edges over
  `deps/verdi-raft/theories` @ a3375e8 (pin re-verified by
  `git rev-parse`; each Interface mapped to its Proof file, closure
  diffed against the INVARIANT INDEX's proved rows). Result: **23
  unported proof files, ~9,760 upstream lines** — far beyond one unit.
  Two corrections to the unit-5 proposal (the lesson pays again):
  (a) `LeaderLogsLogMatching` was slated for unit 7 but is a DIRECT
  import of `LogsLeaderLogsProof.v`, so it must land before GAP-7b;
  (b) eight files the proposal never named are in the closure:
  `UniqueIndices` (30L), `LeaderSublog` (554L), base `LogMatching`
  itself (1,521L — the proposal's open question, answered YES),
  `LeaderLogsSublog` (398L), `AllEntriesIndicesGt0` (195L), and the
  NextIndexSafety feeder chain `AppendEntriesRequestReplyCorrespondence`
  (429L) + `AppendEntriesRequestsCameFromLeaders` (239L) +
  `AppendEntriesLeader` (443L) + `AppendEntriesReplySublog` (79L).
  Msg-ghost check: NOTHING in the closure imports RaftMsgRefinement
  (grep over the closure's files) — GAP-2 stays untouched again.
  Dependency waves (leaves-first; [deps] = unported deps only):
  - W1 (deps all ported): LeaderLogsSorted 227, UniqueIndices 30,
    LeaderSublog 554, AllEntriesIndicesGt0 195,
    LeadersHaveLeaderLogsStrong 278, AERReplyCorrespondence 429,
    AECameFromLeaders 239, AllEntriesTermSanity 185,
    LeaderLogsLogProperties 179;
  - W2: LogMatching 1521 [UniqueIndices, LeaderSublog],
    LeaderLogsSublog 398 [LeaderSublog], AppendEntriesLeader 443
    [AECameFromLeaders];
  - W3: LeaderLogsContiguous 237 [LogMatching],
    RefinedLogMatchingLemmas 230 [LogMatching, AllEntriesIndicesGt0],
    AEReplySublog 79 [AERReplyCorrespondence, AppendEntriesLeader];
  - W4: LeaderLogsLogMatching 647 [LogMatching, LeaderLogsSorted,
    LeaderLogsSublog, LeaderLogsContiguous], NextIndexSafety 323
    [AEReplySublog];
  - W5: AERLeaderLogs 621 [LHLLStrong, LogMatching, NextIndexSafety],
    LogsLeaderLogs 848 [LeaderLogsSorted, Contiguous, LLLogMatching,
    RefinedLogMatchingLemmas, LHLLStrong, NextIndexSafety,
    LLLogProperties];
  - W6: AllEntriesLeaderLogsTerm 342 [AERLeaderLogs],
    **LeaderLogsPreserved 263 (GAP-7b)** [LogsLeaderLogs];
  - W7: AllEntriesLog 1089 [LogsLeaderLogs, AERLeaderLogs,
    RefinedLogMatchingLemmas, AllEntriesLeaderLogsTerm, Contiguous,
    Sorted, AllEntriesTermSanity];
  - W8: **AllEntriesVotesWithLog 356 (GAP-7a)** [AllEntriesLog].
- 2026-08-22 [AGENT] UNIT-6 SCOPE (the largest self-contained prefix
  honestly one unit, at predecessor scale ~1,300-3,000 upstream
  lines/unit): the LOG-MATCHING CORE — `leaderLogs_sorted` (227, GAP-5a)
  → `unique_indices` (30) → `leader_sublog` (554, BASE) →
  `log_matching` (1,521, BASE — the T3-named log-matching invariant) →
  `leaderLogs_contiguous` (237, GAP-5b) → `allEntries_indices_gt0`
  (195) → `refined_log_matching_lemmas` (230 — the refined bridge both
  GAP-7 subtrees consume). 7 proof files, 2,994 upstream lines; every
  dep inside the prefix or already proved (verified against the wave
  table). Closes GAP-5 and answers the base-log_matching question;
  unblocks W2+ of the remainder. THE REMAINDER (16 files, ~6,766
  lines) is the unit-7/8 charter, recorded in this unit's final entry.
  File plan: new `LogMatching.lean` (imports CreationRing), wired into
  VerdiCompat.lean from birth; spec lemmas beside their siblings in
  ElectionSpecLemmas.lean only where a second consumer exists.
- 2026-08-22 Slice 31: `LogMatching.lean` opened — `leaderLogs_sorted`
  (LeaderLogsSortedInterface.v:9-13 1:1, GAP-5a; the only real case is
  the RVR win snapshotting the winner's own log, sorted via
  `sorted_host_lifted` + `handleRequestVoteReply_log` — everything else
  through a ghost-unchanged step helper `leaderLogs_sorted_of_update`)
  and BASE `UniqueIndices` (UniqueIndicesInterface.v:9-20 1:1, both
  conjuncts; no induction — a direct corollary of `logs_sorted_invariant`
  via the constructive `sorted_uniqueIndices`, CommonTheorems.v:761-768,
  proved by `List.Pairwise` directly per GAP-4 discipline). Wired into
  VerdiCompat.lean (sweep covers it from birth: 1546 decls within
  [propext, Quot.sound], build green). [AGENT] The unit-4 `subst`
  gotcha re-confirmed: `heq : h = p.pDst` eliminates the LEFT variable;
  and a direct obligation case needs
  `replace hin : … ∈ (st' h).1.leaderLogs := hin` before `rw [hst h]`
  (the anonymous-constructor `.nwState` is only definitionally `st'`).
- 2026-08-22 Slice 32: `leader_sublog` (LeaderSublogInterface.v:8-27
  1:1, BASE — fifth real base instantiation; upstream proof 554 lines).
  The two `RefinementCommonTheorems.v` lemmas ported 1:1
  (`candidateEntries_wonElection` :19-52,
  `wonElection_candidateEntries_rvr` :54-96) and delivered at base level
  as FOUR `lower_prop` consumers (`candidate_entries_lowered` /`_rvr`/
  `_nw`/`_nw_rvr`, LeaderSublogProof.v:212-443) — the first base-level
  consumers of the CandidateEntries chain. Invariant proof: a
  transport helper `leader_sublog_of_update` (upstream's
  leader_sublog_invariant_subset, :85-121) covers timeout/AER/RV/dGS;
  client_request rides `one_leader_per_term_invariant` (two same-term
  leaders coincide — upstream's exfalso), append_entries rides
  reject-of-not-follower + the log cases, do_leader's fresh AE packets
  resolve through the HOST conjunct on the sender's own log
  (doLeader_messages), and the RVR win case is
  `handleRequestVoteReply_leader_transition` +
  `candidate_entries_lowered_rvr`/`_nw_rvr` — upstream's argument
  without its dedup_not_in_cons split (our transition lemma already
  yields the src-consed tally). Build green, sweep 1571.
- 2026-08-22 Slice 33: the log-matching SUPPORT LAYER — the
  CommonTheorems.v slices LogMatchingProof.v rides, constructive
  inductions per GAP-4: entries_match refl/sym, uniqueIndices_elim_eq
  (:12-22), rachet (:726), findAtIndex intro/None/uniq_equal
  (:741/:269/:540), removeAfterIndex_le_In (:168),
  findGtIndex_sufficient/_max (:334/:532), S_maxIndex_not_in (:74),
  maxIndex_app (:399), maxIndex_removeAfterIndex (:417),
  contiguous_range_exact_lo (:349), **entries_match_scratch**
  (:1133, minus upstream's vacuous 0≠0 conjunct, docstring-noted) and
  **entries_match_append** (:1196) — the two big entries_match engines —
  and removeIncorrect_new_contiguous (:447). [AGENT] The unit-4 omega
  gotcha bit ~10 times (goals/hyps through the term/logIndex abbrevs);
  resolved with explicit Nat.lt/le lemmas throughout, as recorded.
  Build green, sweep 1600.
- 2026-08-22 Slice 34: **`log_matching_invariant` — LOG MATCHING (T3),
  BASE** (LogMatchingProof.v:1495-1515; upstream 1,521 lines; statements
  are Properties.lean's P1 defs, NOT redefined — proved, discharging
  `LogMatchingStatement` natively as `logMatchingStatement_holds`,
  exactly like unit 2's OneLeaderPerTerm). Structure: (a) the
  whole-invariant transport `log_matching_state_same_packet_subset`
  (:47-96) kills timeout/RV/RVR/AER/dGS/state-same/reboot; (b)
  client_request via `handleClientRequest_entries_match` (:722-749 —
  leader_sublog + the impossible maxIndex+1 index) +
  one_leader_per_term; (c) do_leader via `doLeader_messages_full` (a
  new exact-shape spec lemma: every replica message is
  `AE ct me pli (findAtIndex-term) (findGtIndex log pli) ci`), a
  packet classifier, and per-quadrant clause-4 lemmas
  (`hvs_fresh`/`hfresh_vs_old`/fresh-fresh — upstream
  doLeader_log_matching_nw :196-458); (d) `handleAppendEntries_log_matching`
  (:1152-1493, the subtree's centerpiece): unchanged→transport,
  pli=0→`entries_match_scratch`, splice→`entries_match_append` +
  `removeIncorrect_new_contiguous`, with the (pli, plt) PIVOT entry
  crossing between the incoming entries and the receiver's kept prefix
  in the nw clauses. Build green, sweep 1623; zero sorry (grep).
- 2026-08-22 Slice 35: the unit's remainder — `leaderLogs_contiguous`
  (LeaderLogsContiguousInterface.v:9-12 1:1, GAP-5b; RVR win case rides
  `logs_contiguous`, the lifted base log-matching — 4th real lift_prop
  consumer), `allEntries_indices_gt_0`
  (AllEntriesIndicesGt0Interface.v:8-11 1:1; the two allEntries WRITERS
  characterized by new cases lemmas —
  `update_elections_data_client_request_allEntries_cases` (fresh entry
  at maxIndex+1) and `_appendEntries_allEntries_cases` (the request's
  own entries, via `handleAppendEntries_reply_entries`: every reply
  echoes the request's list); the AE case rides `tai_nw_lifted` (5th
  lift_prop consumer)), and the TEN
  `refined_log_matching_lemmas` interface fields as standalone theorems
  (RefinedLogMatchingLemmasInterface.v:9-113, D3 class-dissolve):
  entries contiguous/gt0/sorted × nw/host, entries_match host/nw_1/
  nw_host, allEntries_gt_0 — the lifted bridge BOTH GAP-7 subtrees
  consume. Build green, sweep 1652. GAP-5 IS CLOSED.
- 2026-08-22 AxCheck curated pins added for eight unit-6 headliners
  (leaderLogs_sorted / UniqueIndices / leader_sublog / log_matching /
  logMatchingStatement_holds / leaderLogs_contiguous /
  allEntries_indices_gt_0 / entries_match_nw_host invariants), captured
  from a fresh capped `#print axioms` probe — all [propext, Quot.sound].
  Build green with pins.
- 2026-08-22 CHECKPOINT (recomputed at this tip, 5 slices since the
  unit-6 opening): `git log f64d9b21..HEAD --oneline | wc -l` = 43
  commits; fresh capped `lake build` green, `AxCheck sweep: 1652
  declarations across VerdiCompat modules, axiom set within
  [propext, Quot.sound]`; `grep -c "sorry\|native_decide"` over
  LogMatching.lean: 0 (exit 1, no matches); LogMatching.lean = 2565
  lines (wc). Unit-6 scope state: leaderLogs_sorted ✓, UniqueIndices ✓,
  leader_sublog ✓, log_matching ✓ (+Statement), leaderLogs_contiguous ✓,
  allEntries_indices_gt_0 ✓, refined_log_matching_lemmas ✓ — the full
  scoped prefix. Remaining: gate, final entry + unit-7 charter.

- 2026-08-22 Unit-6 final gate: `GOLEAN_ALLOW_NO_DIFF=1
  GOLEAN_MEM_MAX=24G scripts/ci` — **RESULT: PASS, exit 0** (log:
  `artifacts/ci-arc3-unit6.log`, gitignored; the no-diff notes are the
  allowed docs+compat hatch — unit 6 touched only `compat/verdi/**` +
  this log). The report-only comparator-landmark note now reads
  "56 theorems @ 1730567a2d3f, 48 commit(s) ago" — same
  operator-merge-time flag as units 1-5; nothing in this unit touches a
  designated statement or Challenge's closure (statement-TCB step ok).
  Diffharness fixture pin re-verified fresh out-of-build:
  `diffharness: OK: fixtures/handlers-n3.tsv matches regenerated output
  (320 cases)`.

## Final entry — unit 6 complete (2026-08-22, tip = this commit)

**Proved at tip** — the LOG-MATCHING CORE, the largest self-contained
prefix of the honest GAP-7 closure (derivation in the unit-6 opening
entry): 7 upstream proof files, 2,994 upstream lines, statements 1:1
with their Interface files @ a3375e8 (log_matching's statement is
Properties.lean's P1 def, proved not redefined). Zero
sorry/native_decide in campaign files (grep; sweep-enforced: 1652
declarations within [propext, Quot.sound], plus eight new curated
pins). `#print axioms` verbatim (fresh capped `lake env lean` probe):

```
'VerdiCompat.Raft.leaderLogs_sorted_invariant' depends on axioms: [propext, Quot.sound]
'VerdiCompat.Raft.UniqueIndices_invariant' depends on axioms: [propext, Quot.sound]
'VerdiCompat.Raft.leader_sublog_invariant_invariant' depends on axioms: [propext, Quot.sound]
'VerdiCompat.Raft.log_matching_invariant' depends on axioms: [propext, Quot.sound]
'VerdiCompat.Raft.logMatchingStatement_holds' depends on axioms: [propext, Quot.sound]
'VerdiCompat.Raft.leaderLogs_contiguous_invariant' depends on axioms: [propext, Quot.sound]
'VerdiCompat.Raft.allEntries_indices_gt_0_invariant' depends on axioms: [propext, Quot.sound]
'VerdiCompat.Raft.entries_match_nw_host_invariant' depends on axioms: [propext, Quot.sound]
```

Inventory: `LogMatching.lean` (2,565 lines) — `leaderLogs_sorted`
(GAP-5a) and `leaderLogs_contiguous` (GAP-5b, closing GAP-5), base
`UniqueIndices`, base `leader_sublog` (with the four lowered
CandidateEntries consumers — the first base-level consumers of the
ghost chain), **base `log_matching` — LOG MATCHING, a T3-named
invariant — discharging `LogMatchingStatement` natively**
(`logMatchingStatement_holds`, the second Properties.lean transfer
target down, after unit 2's OneLeaderPerTerm), `allEntries_indices_gt_0`,
and the ten `refined_log_matching_lemmas` fields — the lifted bridge
both GAP-7 subtrees consume. Support layer: the entries_match engines
(`entries_match_scratch`/`_append`), contiguity machinery
(`contiguous_range_exact_lo`, `removeIncorrect_new_contiguous`), and
findAtIndex/findGtIndex/removeAfterIndex lemmas — all constructive
(GAP-4 discipline). Two new lift_prop consumers this unit
(`logs_contiguous`, `tai_nw_lifted`; five total on the lane). The
INVARIANT INDEX above is current (41 data rows, recomputed by
`grep -c "^| "` minus the header — correcting this entry's first
draft, which said 43 unrecomputed).

**Honestly open (carried + new):**
- GAP-1 (primed variants): STILL never triggered — no unit-6 proof
  needed one; carried.
- GAP-2 (msg-ghost): NOT in the honest closure of either GAP-7 target
  (verified by grep over the closure files at unit start); carried
  untouched.
- GAP-4: carried; unit 6 hit the omega-on-abbrev class ~10 times and
  the sweep's LawfulBEq class 0 times (beq handled via
  `simp only [beq_iff_eq]`, which stays within the axiom set).
- GAP-5: **CLOSED** (leaderLogs_sorted + leaderLogs_contiguous).
- GAP-6 (leader_completeness proof) and GAP-7a/b: carried — the
  remainder below is their charter.

**Next units' charter (Arc 3, unit 7 — proposal, from the wave table in
the unit-6 opening entry; re-derive before starting, per standing
lesson):** the REMAINDER is 16 files / ~6,766 upstream lines — two
units:
- **Unit 7 — the AppendEntries feeder chain + leaderLogs assembly**
  (~3,200 lines): W1 leaves `leadersHaveLeaderLogs_strong` (278),
  `appendEntries_request_reply_correspondence` (429),
  `appendEntries_requests_came_from_leaders` (239),
  `allEntries_term_sanity` (185), `leaderLogs_logProperties` (179);
  then `leaderLogs_sublog` (398), `appendEntries_leader` (443),
  `appendEntriesReply_sublog` (79), `nextIndex_safety` (323),
  `leaderLogs_logMatching` (647 — required by LogsLeaderLogs, my
  closure's correction to the unit-5 proposal).
- **Unit 8 — the GAP-7 assembly** (~3,566 lines):
  `appendEntries_request_leaderLogs` (621), `LogsLeaderLogs` (848) →
  **`leaderLogs_preserved` (GAP-7b)** (263),
  `allEntries_leaderLogs_term` (342), `AllEntriesLog` (1,089) →
  **`allEntries_votesWithLog` (GAP-7a)** (356). Then GAP-6
  (`prefix_within_term` + `leader_completeness`'s proof) beyond.
Same conventions; successors re-verify this unit's claims fresh (build
+ sweep count 1652 + the eight-headliner probe above + hatch grep over
LogMatching.lean).

## Unit 7 — the AppendEntries feeder chain (2026-08-22, coordinator-accepted charter)

Coordinator additions folded in: same conventions in full; context-strain
stop rule acknowledged (clean-slice-boundary handoff if retrieval
degrades); unit-8 charter at unit end.

- 2026-08-22 SUCCESSOR-STYLE RE-VERIFICATION of unit 6 (recomputed,
  same worker continuing under the unit-7 charter): tip 86d372c0, tree
  clean; capped `lake build` green (cached), sweep re-derived by fresh
  capped `lake env lean AxCheck.lean` — verbatim `AxCheck sweep: 1652
  declarations across VerdiCompat modules, axiom set within
  [propext, Quot.sound]`; fresh capped `#print axioms` probe:
  `log_matching_invariant`, `logMatchingStatement_holds`,
  `leaderLogs_contiguous_invariant` all
  `depends on axioms: [propext, Quot.sound]` verbatim; hatch grep
  (`sorry|native_decide|^axiom| axiom `) over LogMatching.lean: 1 hit,
  line 156, docstring prose. All claims hold; building on them.
- 2026-08-22 [AGENT] UNIT-7 CLOSURE, re-derived fresh from the ten
  chartered targets (transitive `Require Import` walk @ a3375e8, pin
  re-verified; diffed against the 37 now-ported proof files): the
  closure is EXACTLY the ten targets — no new files this time (the
  unit-6 correction pass already surfaced them all), no msg-ghost
  anywhere (grep). 3,200 upstream lines, self-contained. In-unit waves:
  - W1 (deps all ported): LeadersHaveLeaderLogsStrong 278,
    AERReplyCorrespondence 429, AECameFromLeaders 239,
    AllEntriesTermSanity 185, LeaderLogsLogProperties 179,
    LeaderLogsSublog 398;
  - W2: AppendEntriesLeader 443 [AECameFromLeaders],
    LeaderLogsLogMatching 647 [LeaderLogsSublog];
  - W3: AppendEntriesReplySublog 79 [AERRC, AEL];
  - W4: NextIndexSafety 323 [AEReplySublog].
  File plan: new `AppendEntriesChain.lean` (imports LogMatching), wired
  into VerdiCompat.lean from birth; spec lemmas promoted to
  ElectionSpecLemmas.lean only at a second consumer.
- 2026-08-23 Slice 36: `AppendEntriesChain.lean` opened — the W1 ghost
  leaves: `allEntries_term_sanity` (AllEntriesTermSanityInterface.v:8-12
  1:1; new term-aware allEntries cases lemmas keyed to the handler
  result — `update_elections_data_client_request/appendEntries_
  allEntries_term_cases` — plus `handleAppendEntries_reply_true`: a
  true reply carries the request's term, which the responder's new term
  dominates via `advanceCurrentTerm_ge`), `log_properties_hold_on_
  leader_logs` (LeaderLogsLogPropertiesInterface.v:9-17 1:1 — the
  HIGHER-ORDER snapshot principle: any reachability-closed log property
  holds of every leaderLog, since the RVR snapshot is the reachable
  pre-state's own log), and `leaders_have_leaderLogs_strong`
  (LeadersHaveLeaderLogsStrongInterface.v:8-16 1:1; client_request
  stacks one own-term entry on es, the fresh win takes es = []).
  [AGENT] Gotchas re-hit and resolved: refined-state spec calls need
  `.2` (seven sites); `nomatch` on a `true = true` hypothesis LEAKS its
  error through `try` — `cases hmr` closes impossible Bool equations
  and passes trivial ones cleanly (recorded for successors). Build
  green, sweep 1689 (was 1652).
- 2026-08-23 Slice 37: **`append_entries_request_reply_correspondence`**
  (AERRCorrespondenceInterface.v:9-20 1:1, BASE; upstream 429 lines) —
  every true AppendEntriesReply corresponds to an equivalent REACHABLE
  network still carrying a matching request. New reachability
  machinery: `reachable_dup` / `reachable_drop_suffix` /
  **`subset_reachable`** (Verdi's DupDropReordering `dup_drop_reorder`
  re-proved directly: dup the members in, drop the original pool) —
  the first campaign use of `RIR_step_failure` with the fault model's
  dup/drop/reboot steps. Proof: each obligation RE-PLAYS its step from
  the IH's equivalent network (RIR constructors applied directly, the
  handler equation transported along `net₀.nwState = net.nwState`);
  the CREATION case (an accepted AppendEntries) first DUPLICATES the
  consumed request via `StepFailure_dup`, then delivers one copy —
  upstream's exact construction; state-same rides `subset_reachable`,
  reboot rides `StepFailure_reboot` + funext (the def's
  state-function equality). [AGENT] Judgment call: `subset_reachable`
  is proved from scratch (~50 lines) instead of porting Verdi's
  generic DupDropReordering module — single consumer, and the direct
  induction is smaller than the module's step-star plumbing; lift
  later per the promotion-ledger rule if the msg-ghost arcs need it.
  Build green, sweep 1700.
- 2026-08-23 Slice 38a: `appendEntries_requests_came_from_leaders`
  (AECameFromLeadersInterface.v:8-15 1:1, ghost) — every in-flight
  AppendEntries' sender holds a leaderLog at the packet's term. The
  do_leader creation case: `doLeader_messages_leader` (only a leader
  sends) + `leaders_have_leaderLogs_invariant` at the sender's own term
  (doLeader_messages pins the body's term to it); every other case is
  the sender-side transport `came_from_leaders_transport` (leaderLogs
  only grow — the RVR case rides the `_leaderLogs_old` lemma).
  Build green, sweep 1713.
- 2026-08-23 Slice 38b: `leaderLogs_sublog`
  (LeaderLogsSublogInterface.v:8-14 1:1, ghost; upstream 398 lines) —
  any snapshot entry bearing a leader's current term is in that
  leader's log. New: `handleRequestVoteReply_RVR_spec` (the three-way
  outcome; [AGENT] gotcha for successors: `repeat' split at h` on
  handleRequestVoteReply×advanceCurrentTerm yields SEVEN branches —
  the shared `t >? ct` guard does NOT re-split (no contradiction
  branch), the `if voteGranted`/`if won` record fields DO, and the
  match's non-candidate arms COLLAPSE to one default with
  `st.type = Candidate → False`; enumerate with lean_goal before
  writing bullets) and `lifted_leader_sublog_host` (6th lift_prop
  consumer). The RVR win case: own old snapshot at the win term dies
  on the leaderLogs term-sanity pair; someone else's dies on
  `leaderLogs_candidateEntries` + `wonElection_candidateEntries_rvr`
  over the consumed grant; the fresh snapshot IS the log. Build green,
  sweep 1728.
- 2026-08-23 Slice 39: `appendEntries_leader`
  (AppendEntriesLeaderInterface.v:8-16 1:1, ghost; upstream 443 lines)
  and **`append_entries_reply_sublog`**
  (AppendEntriesReplySublogInterface.v:8-16 1:1, BASE) — every
  in-flight AE entry (resp. every true-reply entry) bearing a leader's
  current term is in that leader's log. New: `lifted_one_leader_per_term`
  (7th lift consumer), `lowered_appendEntries_leader` (a lower_prop
  consumer), and **`rvr_win_votes`** — PROMOTED from
  one_leaderLog_per_term's inline `hwin` per the promotion-ledger rule
  (2nd consumer; unit-4's inline copy left as-is — consolidation
  candidate for a cleanup slice). [AGENT] JUDGMENT CALL (logged, not a
  deviation from the lattice): upstream's RVR case is the FIRST
  genuine consumer of the GAP-1 primed obligations
  (`refined_raft_net_invariant_request_vote_reply'` + post-state
  one_leaderLog_per_term_host). Instead of porting the primed layer,
  the same lattice facts close the case in the PRE-state:
  `append_entries_came_from_leaders` gives the AE-sender's standing
  snapshot, `one_leaderLog_win_host` + `rvr_win_votes` force
  sender = winner, and `leaderLogs_currentTerm_sanity_candidate` kills
  the candidate-with-own-term-snapshot. GAP-1 REMAINS UNTRIGGERED; the
  primed layer stays port-on-first-need. `append_entries_reply_sublog`
  is the correspondence's payoff: resurrect the request, read the
  entries off the leader's log. Build green, sweep 1745.
- 2026-08-23 CHECKPOINT (recomputed at this tip; 5 slice-units since
  the unit-7 opening: 36, 37, 38a, 38b, 39): `git log f64d9b21..HEAD
  --oneline | wc -l` = 51 commits + this one; capped `lake build`
  green, `AxCheck sweep: 1745 declarations across VerdiCompat modules,
  axiom set within [propext, Quot.sound]`; `grep -c
  "sorry\|native_decide"` over AppendEntriesChain.lean: 0 (exit 1);
  AppendEntriesChain.lean = 2,141 lines (wc). Unit-7 state:
  allEntries_term_sanity ✓, log_properties_hold_on_leader_logs ✓,
  leaders_have_leaderLogs_strong ✓, AERReplyCorrespondence ✓ (+
  subset_reachable machinery), AECameFromLeaders ✓, leaderLogs_sublog ✓,
  appendEntries_leader ✓, appendEntriesReply_sublog ✓. Remaining:
  nextIndex_safety (323L), leaderLogs_logMatching (647L), pins, INDEX,
  gate, final entry + unit-8 charter.
- 2026-08-23 Slice 40: `nextIndex_safety`
  (NextIndexSafetyInterface.v:8-11 1:1, BASE) — a leader's nextIndex
  estimates never point past its log. New StructTact machinery:
  `assoc_assoc_set_same/_diff` + `assoc_set_same/diff_default`
  (get_set_* analogues), per-handler nextIndex-preservation lemmas
  (incl. `applyEntries_nextIndex` by induction), the case lemma
  `handleAppendEntriesReply_nextIndex` (:118-139 — untouched, or
  assoc_set to max(getNextIndex, maxIndex es + 1) on success / pred on
  failure) and `handleRequestVoteReply_nextIndex` (:199-210 — kept, or
  reset to [] at a win, where the default getNextIndex = maxIndex log
  is safe outright). The success case rides
  `append_entries_reply_sublog`: the replied entries are in the
  leader's own log, so maxIndex es ≤ maxIndex log via sorted
  maxIndex_is_max. Build green, sweep 1785.
- 2026-08-23 Slice 41: **`leaderLogs_entries_match`** (host ∧ nw,
  LeaderLogsLogMatchingProof.v:9-52 defs 1:1; the interface half
  projected as `leaderLogs_entries_match_invariant`,
  LeaderLogsLogMatchingInterface.v:9-13) — host logs and in-flight
  entries match every leaderLog snapshot; upstream 647 lines. New
  support: `maxTerm_is_max`, `entries_match_nil`/
  `entries_match_cons_gt_maxTerm`/`entries_match_cons_sublog`
  (:63-118), `lifted_log_matching_nw_prev` (the prevLog-resolution
  piece RLML doesn't carry). The cases: client_request stacks the
  own-term entry via gt-maxTerm (own snapshots, term-sanity pair) or
  cons-sublog (`leaderLogs_sublog` pays off); append_entries re-runs
  the unit-6 scratch/splice engines against snapshots with the NW half
  of the induction supplying the matched-pair clauses; RVR's fresh
  snapshot IS the winner's log (lifted base log matching, both
  halves); do_leader's replica packets resolve their prevLog inside
  the snapshot via `leaderLogs_contiguous` + the host half. Build
  green, sweep 1805. THE UNIT-7 SCOPE IS COMPLETE (10/10 files).
- 2026-08-23 Unit-7 final gate: `GOLEAN_ALLOW_NO_DIFF=1
  GOLEAN_MEM_MAX=24G scripts/ci` — **RESULT: PASS, exit 0** (log:
  `artifacts/ci-arc3-unit7.log`, gitignored; no-diff notes are the
  allowed docs+compat hatch — unit 7 touched only `compat/verdi/**` +
  this log). The report-only comparator-landmark note now reads
  "56 theorems @ 1730567a2d3f, 59 commit(s) ago" — same
  operator-merge-time flag as units 1-6; nothing here touches a
  designated statement or Challenge's closure (statement-TCB step ok).

## Final entry — unit 7 complete (2026-08-23, tip = this commit)

**Proved at tip** — the AppendEntries feeder chain, ALL TEN targets of
the re-derived closure (which was exactly the charter's ten files,
3,200 upstream lines), statements 1:1 with their Interface files @
a3375e8; zero sorry/native_decide in campaign files (grep;
sweep-enforced: 1805 declarations within [propext, Quot.sound], plus
ten new curated pins). `#print axioms` verbatim (fresh capped
`lake env lean` probe):

```
'VerdiCompat.Raft.allEntries_term_sanity_invariant' depends on axioms: [propext, Quot.sound]
'VerdiCompat.Raft.log_properties_hold_on_leader_logs_invariant' depends on axioms: [propext, Quot.sound]
'VerdiCompat.Raft.leaders_have_leaderLogs_strong_invariant' depends on axioms: [propext, Quot.sound]
'VerdiCompat.Raft.append_entries_request_reply_correspondence_invariant' depends on axioms: [propext, Quot.sound]
'VerdiCompat.Raft.append_entries_came_from_leaders_invariant' depends on axioms: [propext, Quot.sound]
'VerdiCompat.Raft.leaderLogs_sublog_invariant' depends on axioms: [propext, Quot.sound]
'VerdiCompat.Raft.append_entries_leader_invariant' depends on axioms: [propext, Quot.sound]
'VerdiCompat.Raft.append_entries_reply_sublog_invariant' depends on axioms: [propext, Quot.sound]
'VerdiCompat.Raft.nextIndex_safety_invariant' depends on axioms: [propext, Quot.sound]
'VerdiCompat.Raft.leaderLogs_entries_match_invariant' depends on axioms: [propext, Quot.sound]
```

Inventory: `AppendEntriesChain.lean` (3,206 lines, wc). Highlights:
the higher-order snapshot principle `log_properties_hold_on_leader_logs`;
`subset_reachable` (Verdi's DupDropReordering re-proved directly) and
the dup-step correspondence — the campaign's first real use of the
fault model's dup/drop/reboot legs; `rvr_win_votes` PROMOTED from
unit 4's inline hwin (2nd consumer); `leaderLogs_sublog` and
`appendEntries_leader` (the latter via the PRE-STATE
`one_leaderLog_win_host` route — GAP-1 stays untriggered, logged
judgment call at slice 39); `nextIndex_safety` with the assoc get/set
machinery; and the exit theorem `leaderLogs_entries_match` (host ∧ nw)
riding the unit-6 entries_match engines and RLML bridge. The INVARIANT
INDEX above is current (51 data rows, recomputed: 52 `^| `-lines minus
the header). New lift_prop consumers this unit:
`lifted_one_leader_per_term`, `lifted_leader_sublog_host`,
`lifted_log_matching_nw_prev` (+ the tai_nw/came-from-leaders uses) —
eight total on the lane.

**Honestly open (carried):**
- GAP-1 (primed variants): STILL never triggered — slice 39's judgment
  call closed upstream's only primed-variant consumer so far in the
  pre-state; carried as port-on-first-need.
- GAP-2 (msg-ghost): untouched (absent from this unit's closure, and
  from unit 8's targets per the unit-6 wave table — RE-VERIFY at unit-8
  start).
- GAP-4 (classical-list doctrine question), GAP-6
  (leader_completeness proof), GAP-7a/b: carried unchanged.

**Next unit's charter (Arc 3, unit 8 — proposal, per the unit-6 wave
table; RE-DERIVE the closure fresh before proving, as always):** the
GAP-7 assembly (~3,566 upstream lines):
`appendEntries_request_leaderLogs` (621) → `allEntries_leaderLogs_term`
(342), `LogsLeaderLogs` (848) → **`leaderLogs_preserved` (GAP-7b)**
(263), then `AllEntriesLog` (1,089) → **`allEntries_votesWithLog`
(GAP-7a)** (356). If the honest closure or session budget forces a
split, the self-contained prefix is AERLeaderLogs + LogsLeaderLogs +
leaderLogs_preserved (GAP-7b closed), leaving the AllEntries side for
unit 9. Beyond: GAP-6 (`prefix_within_term` +
`leader_completeness`'s proof). Same conventions; successors re-verify
this unit fresh (build + sweep 1805 + the ten-headliner probe above +
hatch grep over AppendEntriesChain.lean).

## Unit 8 — the GAP-7 assembly (2026-08-23, coordinator-accepted charter)

Charter per the predecessor's posted proposal: the GAP-7 assembly —
`appendEntries_request_leaderLogs` → `allEntries_leaderLogs_term`,
`LogsLeaderLogs` → **`leaderLogs_preserved` (GAP-7b)**, `AllEntriesLog`
→ **`allEntries_votesWithLog` (GAP-7a)** — with the recorded split
point (AERLeaderLogs + LogsLeaderLogs + leaderLogs_preserved = a
branch-complete prefix) if the honest budget forces one. GAP-2
re-verified at THIS unit's closure derivation, not inherited.

- 2026-08-23 SUCCESSOR RE-VERIFICATION of unit 7 (recomputed, fresh
  reader): tip 44b0794b, tree clean, branch `campaign-arc3`;
  `deps/verdi-raft` pin re-verified `a3375e867326a82225e724cc1a7b4758b029376f`
  (read from the MAIN checkout as before). Fresh capped `lake build`
  (24G) green ("Build completed successfully (45 jobs)"); the sweep
  line in that build was a cache replay, so re-derived by a fresh
  capped `lake env lean AxCheck.lean`, which printed verbatim
  `AxCheck sweep: 1805 declarations across VerdiCompat modules, axiom
  set within [propext, Quot.sound]`. Fresh `#print axioms` probe
  (capped `lake env lean`, repo-local scratch):
  `leaderLogs_entries_match_invariant`,
  `append_entries_request_reply_correspondence_invariant`,
  `leaderLogs_sublog_invariant` all
  `depends on axioms: [propext, Quot.sound]` verbatim. Hatch grep
  (`sorry|native_decide|^axiom| axiom `) over AppendEntriesChain.lean:
  0 hits. All claims hold; building on them.
- 2026-08-23 [AGENT] UNIT-8 CLOSURE, re-derived fresh from the six
  chartered targets (`Require Import` walk @ a3375e8, pin re-verified
  by `git rev-parse`; every imported Interface diffed against the
  INVARIANT INDEX's proved rows): the closure is EXACTLY the six
  target files — no new files (the unit-6 correction pass holds), and
  **no msg-ghost**: `grep -l "MsgRefinement\|GhostLog"` over all 12
  closure files (6 Proof + 6 Interface) returns nothing, so GAP-2
  stays untouched at the very unit the charter flagged as likeliest
  first contact (AllEntriesLog is clean). Honest line count RECOMPUTED
  from `wc -l` at the pin: 621+848+263+342+1089+356 = **3,519**
  upstream lines (the charter's ~3,566 was the wave table's sum,
  not re-derived). In-unit dependency order (all other deps ported):
  - W1: AERLeaderLogs 621 [LHLLStrong ✓, Sorted ✓, LogMatching ✓,
    NextIndexSafety ✓] and LogsLeaderLogs 848 [LeaderLogsSorted ✓,
    Contiguous ✓, LLLogMatching ✓, RLML ✓, LHLLStrong ✓,
    NextIndexSafety ✓, Sorted ✓, LLLogProperties ✓] — mutually
    independent (LogsLeaderLogs does NOT import AERLeaderLogs);
  - W2: LeaderLogsPreserved 263 (GAP-7b) [LogsLeaderLogs;
    LLTermSanity ✓, LLCandidateEntries ✓, OneLeaderLogPerTerm ✓,
    VotesCorrect ✓, CroniesCorrect ✓] and AllEntriesLeaderLogsTerm
    342 [AERLeaderLogs];
  - W3: AllEntriesLog 1089 [LogsLeaderLogs, AERLeaderLogs,
    AllEntriesLeaderLogsTerm; RLML ✓, Contiguous ✓,
    OneLeaderLogPerTerm ✓, LeaderLogsSorted ✓, TermSanity ✓,
    AllEntriesTermSanity ✓];
  - W4: AllEntriesVotesWithLog 356 (GAP-7a) [AllEntriesLog;
    VotesWithLogTermSanity ✓, VotesCorrect ✓,
    VotesVotesWithLogCorrespond ✓].
- 2026-08-23 [AGENT] File plan: new `LeaderLogsAssembly.lean`
  (imports AppendEntriesChain), wired into VerdiCompat.lean from
  birth; spec lemmas promoted to ElectionSpecLemmas.lean only at a
  second consumer, as before. Port order = the wave order above,
  AERLeaderLogs first.
- 2026-08-23 Slice 42: `LeaderLogsAssembly.lean` opened —
  **`append_entries_leaderLogs`**
  (AppendEntriesRequestLeaderLogsInterface.v:9-22 1:1; upstream proof
  621 lines): every in-flight AE's entries split as own-term entries
  atop a prefix of a recorded leaderLog at the packet's term. New:
  StructTact `Prefix` (fixpoint form 1:1) + refl/nil/In, the
  findGtIndex-over-append machinery (sorted_findGtIndex_0,
  findGtIndex_Prefix, findGtIndex_app_in_1/_in_2/_app_eq,
  sorted_app_in_1 — AERLeaderLogsProof.v:374-478),
  `doLeader_messages_nextIndex` (doLeader_spec :304-335 in the
  exact-shape style of doLeader_messages_full but RETAINING pli =
  pred (getNextIndex st host)), `nextIndex_sanity` (:346-372; lifted
  nextIndex_safety + logs_contiguous + findAtIndex_intro), and the
  witness transport `aell_transport` (leaderLogs only grow). The ten
  transport obligations mirror unit 7's came_from_leaders pattern;
  the doLeader CREATION case splits the sender's log over its
  leaders_have_leaderLogs_strong snapshot and classifies the
  findGtIndex cut (top ⇒ disjunct 1 via sorted_app_in_1; snapshot ⇒
  disjunct 2 with Prefix_sane by findGtIndex_app_eq; unresolved ⇒
  origin or nextIndex_sanity contradiction). Build green, sweep 1853
  (was 1805).
- 2026-08-23 Slice 43: the LogsLeaderLogs support layer
  (CommonTheorems.v slices, constructive per GAP-4): four cons-step
  guard-rewrite lemmas (findGtIndex/removeAfterIndex × pos/neg — the
  `unfold`-both-sides trap made explicit), contiguity machinery
  (contiguous_index_singleton, cons_contiguous_sorted, contiguous_app,
  removeAfterIndex_contiguous), **`sorted_mem_eq`** (sorted logs with
  equal member sets coincide — the constructive replacement for
  upstream's sorted_Permutation_eq/NoDup_Permutation route under
  `removeAfterIndex_same_sufficient` :1624), prefix_sorted, upstream's
  `thing2`/`thing`/`thing3` (names kept 1:1 for citation mapping),
  findGtIndex_removeAfterIndex_commute, findGtIndex_app_1/_2,
  findGtIndex_non_empty, removeAfterIndex_in_app/_in_app_l'/
  _maxIndex_sorted/_le/_eq. [AGENT] Gotchas re-hit, resolved per the
  lane record: omega-on-abbrev (×2, explicit Nat lemmas), continuation
  lines indented below the tactic column silently start a new command
  (the sorted_mem_eq parse break).
- 2026-08-23 Slice 44: **`logs_leaderLogs` + `logs_leaderLogs_nw`**
  (LogsLeaderLogsInterface.v:9-30 1:1; upstream proof 848 lines) — the
  host∧nw simultaneous induction (`logs_leaderLogs_inductive`), both
  interface fields delivered. Proof shape: transports
  (`logs_leaderLogs_of_update` + `lll_nw_transport`) cover eight
  handlers; client_request stacks the fresh entry on the
  leaders_have_leaderLogs_strong split; append_entries is the
  centerpiece — a NEW entry's nw witness glues to the pivot's host
  witness (`thing` when a snapshot entry is shared;
  `removeAfterIndex_same_sufficient` + maxIndex when the prevLog sits
  at the snapshot's max; the fresh-cut case re-anchors at the pivot's
  own leader), an OLD entry survives below the cut
  (removeAfterIndex_in_app_l' + removeAfterIndex_le); doLeader
  classifies `findGtIndex log pli` by trichotomy against the witness
  snapshot's max (commute + app_1/app_2 + thing3). [AGENT] Upstream's
  `weak_sanity`/`logs_leaderLogs_nw_weaken` detour is NOT ported
  (docstring-flagged): with the strong nw disjunction, `pli = 0`
  forces the third disjunct outright — disjunct 1 dies on
  `0 > maxIndex`, disjunct 2 on `leaderLogs_contiguous`. Gotchas for
  successors: `set` is a Mathlib tactic — UNAVAILABLE here; use
  `generalize h : lit = x` + `rw [h] at hyp` + pre-derived projection
  equations. And the var=var subst direction bit twice more
  (`rfl`-pattern on `e = enew` keeps e; `subst hll` on `ll' = ll`
  keeps ll' — rw at the hypothesis instead). Build green, sweep 1902
  (was 1853).
- 2026-08-23 Slice 45: **`leaderLogs_preserved` — GAP-7b CLOSED**
  (LeaderLogsPreservedInterface.v:9-15 1:1; upstream proof 263 lines).
  Ten obligations are one ghost-unchanged transport
  (`leaderLogs_preserved_of_update`); the RVR case's four sub-cases:
  old/old → IH; fresh `ll'` → the entry resolves through
  `logs_leaderLogs_invariant` (slice 44's payoff, immediately) and
  `one_leaderLog_per_term_log` identifies the snapshots; fresh `ll` →
  the `wonElection_candidateEntries_rvr` contradiction (unit-6's
  lemma; [AGENT] upstream's separate same-host term-sanity bullet
  (:106-114) is subsumed — the candidate-entries route needs no host
  split, docstring-noted); fresh/fresh → same log, direct. Build
  green, sweep 1907.
- 2026-08-23 CHECKPOINT (recomputed at 90e1cd28; 5 units since the
  unit-8 opening: re-verification+closure, slices 42-45):
  `git log f64d9b21..HEAD --oneline | wc -l` = 61 commits; fresh capped
  `lake build` green with `AxCheck sweep: 1907 declarations across
  VerdiCompat modules, axiom set within [propext, Quot.sound]`;
  `grep -c "sorry\|native_decide"` over LeaderLogsAssembly.lean: 0
  (exit 1); LeaderLogsAssembly.lean = 1,986 lines (wc). Unit-8 state:
  append_entries_leaderLogs ✓ (W1), logs_leaderLogs + nw ✓ (W1),
  **leaderLogs_preserved ✓ (GAP-7b CLOSED)** (W2). Remaining:
  allEntries_leaderLogs_term (342L, W2), AllEntriesLog (1,089L, W3),
  allEntries_votesWithLog (356L, GAP-7a, W4), pins, INDEX, gate.
- 2026-08-23 Slice 46 (76cc6cda): `allEntries_leaderLogs_term`
  (AllEntriesLeaderLogsTermInterface.v:9-15 1:1; upstream 342 lines) —
  slice 42's `append_entries_leaderLogs` pays off immediately: a
  freshly recorded (term, entry) classifies through the packet's
  `es' ++ ll'` split (own-term block ⇒ left disjunct; prefix block ⇒
  the snapshot witness via Prefix_In). [AGENT] The lane's
  `..._allEntries_term_cases` didn't tie the client-request record to
  the fresh entry's term; a sharper local lemma
  (`update_elections_data_client_request_allEntries_head_term`) reads
  it off handleClientRequest_log_full — kept local (single consumer).
  Build green, sweep 1915.
- 2026-08-23 Slices 47-48 (a700a7c9, f7efa59e): **`allEntries_log`**
  (AllEntriesLogInterface.v:10-19 1:1; upstream 1,089 lines — the
  unit's summit). Support: maxIndex_non_empty/maxIndex_le'/
  Prefix_maxIndex_eq/prefix_contiguous, haveNewEntries elims,
  appendEntries_haveNewEntries_false,
  `handleAppendEntries_accept_detail` (SpecLemmas.v:236-280's shape
  with haveNewEntries retained), and seven per-handler
  currentTerm/leaderId movement lemmas (incl. an applyEntries_leaderId
  induction — applyEntries_spec doesn't carry leaderId). [AGENT]
  PROOF-SHAPE CALL (logged; §9 guided re-proof — same invariant
  lattice, re-derived route): upstream's ~500-line append_entries Ltac
  (four bullets of interleaved exfalso battles,
  sorted_app_sorted_app_in1_in2 family, term_ne_in_l2) is replaced by
  TWO containment lemmas — `ae_snapshot_in_newlog` (a host-log member
  of the packet's term-t snapshot is in the new log; per accept-shape
  × prevLog-disjunct analysis) and `ae_own_term_in_newlog` (a host
  entry AT term t reappears inside `es` via the haveNewEntries
  maxIndex bound + log matching + uniqueIndices, or sits below the
  splice) — after which the AE case is: old log-witness destroyed ⇒
  the packet snapshot is the new witness (t0 < t) or the containments
  refute the destruction (t0 = t, via allEntries_leaderLogs_term);
  old snapshot-witness ⇒ ct/leaderId transport; new records ⇒ in the
  new log or nothing was new. Both containment lemmas compiled on
  first attempt. Build green, sweep 1970.
- 2026-08-23 Slice 49: **`allEntries_votesWithLog` — GAP-7a CLOSED**
  (AllEntriesVotesWithLogInterface.v:10-19 1:1; upstream 356 lines) —
  slice 48's payoff: a fresh vote (RV grant / timeout candidacy)
  snapshots the voter's unchanged log, so `allEntries_log` classifies
  every earlier record against it; the vote's term dominates the
  intermediate snapshot's via the grant fine print
  (`update_elections_data_requestVote_votesWithLog_elim_fine`, whose
  fine print comes from `handleRequestVote_vote_change` — the isNone
  guard or an advanced term — upstream's
  handleRequestVote_currentTerm_leaderId'); fresh allEntries records
  sit at/above the recorder's current term, above every recorded vote
  by votesWithLog term sanity. AxCheck pins for the seven unit-8
  headliners (fresh probe, all [propext, Quot.sound]). Build green,
  sweep 1985. INDEX updated: GAP-7a/b rows PROVED + four new rows.
  [AGENT] Gotcha re-confirmed twice more: `subst` on
  `h0 = p.pDst` eliminates h0 (LEFT, projection right) — post-subst
  scripts must reference p.pDst; and the unit-7 nomatch-through-`first`
  leak (put the benign alternative first).
- 2026-08-23 Unit-8 final gate: `GOLEAN_ALLOW_NO_DIFF=1
  GOLEAN_MEM_MAX=24G scripts/ci` — **RESULT: PASS, exit 0** (log:
  `artifacts/ci-arc3-unit8.log`, gitignored; the no-diff notes are the
  allowed docs+compat hatch — unit 8 touched only `compat/verdi/**` +
  this log). The report-only comparator-landmark note now reads
  "56 theorems @ 1730567a2d3f, 70 commit(s) ago" — same
  operator-merge-time flag as units 1-7; nothing in this unit touches
  a designated statement or Challenge's closure (statement-TCB step
  ok).

## Final entry — unit 8 complete (2026-08-23, tip 5fb63040 + this commit)

**Proved at tip — THE GAP-7 ASSEMBLY, BOTH GAPS CLOSED.** All six files
of the re-derived closure (exactly the charter's six, 3,519 upstream
lines recomputed at the pin), statements 1:1 with their Interface files
@ a3375e8; zero sorry/native_decide in campaign files (grep;
sweep-enforced: 1985 declarations within [propext, Quot.sound], plus
seven new curated pins). `#print axioms` verbatim (fresh capped
`lake env lean` probe):

```
'VerdiCompat.Raft.append_entries_leaderLogs_invariant' depends on axioms: [propext, Quot.sound]
'VerdiCompat.Raft.logs_leaderLogs_invariant' depends on axioms: [propext, Quot.sound]
'VerdiCompat.Raft.logs_leaderLogs_nw_invariant' depends on axioms: [propext, Quot.sound]
'VerdiCompat.Raft.leaderLogs_preserved_invariant' depends on axioms: [propext, Quot.sound]
'VerdiCompat.Raft.allEntries_leaderLogs_term_invariant' depends on axioms: [propext, Quot.sound]
'VerdiCompat.Raft.allEntries_log_invariant' depends on axioms: [propext, Quot.sound]
'VerdiCompat.Raft.allEntries_votesWithLog_invariant' depends on axioms: [propext, Quot.sound]
```

Inventory: `LeaderLogsAssembly.lean` (3,965 lines, wc; line numbers at
this tip) — StructTact `Prefix` (:50) + `Prefix_sane` (:82);
**`append_entries_leaderLogs`** (:90, invariant :332) with
`nextIndex_sanity` (:308) and the findGtIndex-over-append machinery;
the constructive LogsLeaderLogs support layer (`sorted_mem_eq` :699 —
the Permutation-free `removeAfterIndex_same_sufficient` spine —
upstream's `thing2`/`thing`/`thing3` :775/:817/:839, names kept 1:1);
**`logs_leaderLogs`/`_nw`** (:1023/:1033, inductive invariant :1605,
interface fields :1785/:1791); **`leaderLogs_preserved` (GAP-7b)**
(:1802, invariant :1842); **`allEntries_leaderLogs_term`** (:1991,
invariant :2066); **`allEntries_log`** (:2623, invariant :3210) with
the two containment lemmas `ae_snapshot_in_newlog` (:2837) /
`ae_own_term_in_newlog` (:2913) and the handler-detail layer;
**`allEntries_votesWithLog` (GAP-7a)** (:3407, invariant :3621). The
INVARIANT INDEX above is current (55 data rows, recomputed:
`grep -c "^| "` = 56 minus the header). 66 commits on the lane
(`git log f64d9b21..HEAD --oneline | wc -l`, recomputed at 5fb63040).

**Honestly open (carried; none counted toward any total):**
- GAP-1 (primed variants): STILL never triggered — no unit-8 proof
  needed one; carried as port-on-first-need.
- GAP-2 (msg-ghost): NOT in unit 8's closure (grep over all 12 closure
  files at unit start — AllEntriesLog, the predicted first contact,
  is clean); carried untouched.
- GAP-4 (classical-list doctrine): carried; unit 8 resolved every
  instance constructively (sorted_mem_eq replacing the
  NoDup_Permutation route is the biggest).
- GAP-5: closed in unit 6. GAP-7a/b: **CLOSED THIS UNIT.**
- GAP-6 (leader_completeness proof): now the ONLY named gap on the
  leader-completeness path; its remaining closure is unit 9's charter
  below.

**Next unit's charter (Arc 3, unit 9 — proposal; RE-DERIVE the closure
fresh before proving, as always):** GAP-6 — `leader_completeness`'s
PROOF. Fresh closure walk @ a3375e8 (this unit's exit derivation):
six unported files, ~3,428 upstream lines, every other dep already
ported: `AllEntriesCandidateEntries` (305; deps all ✓) and
`appendEntriesRequest_term_sanity` (48; Sorted ✓) →
`AllEntriesLeaderSublog` (351) → `AllEntriesLogMatching` (430) →
`PrefixWithinTerm` (1,915 — the heavy one) →
**`leader_completeness`'s proof** (LeaderCompletenessProof.v, 379;
discharges the statement ported in unit 4). If the honest budget
forces a split, the self-contained prefix is the four feeder files
(through AllEntriesLogMatching), leaving PrefixWithinTerm +
LeaderCompleteness for unit 10. Beyond unit 9: the
state-machine-safety cap (StateMachineSafetyProof.v and its closure —
re-derive; GAP-2 msg-ghost is EXPECTED there via the GhostLog* chain,
so the minimal-port-on-first-need clause will likely fire). Same
conventions; successors re-verify this unit fresh (build + sweep 1985
+ the seven-headliner probe above + hatch grep over
LeaderLogsAssembly.lean).

## Unit 9 — GAP-6: leader_completeness's proof (2026-08-23, coordinator-accepted charter)

Charter per the posted proposal, coordinator additions folded in:
context rule ACTIVE (stop at a clean slice boundary at first strain —
PrefixWithinTerm at 1,915L is the flagged point; a mid-unit handoff
there is a fine outcome); when leader_completeness lands, the report
states the T3 ladder plainly; GAP-2 minimal-port-on-first-need if
PrefixWithinTerm surprises.

- 2026-08-23 SUCCESSOR RE-VERIFICATION of unit 8 (recomputed, same
  worker continuing under the unit-9 charter): tip becfe284, tree
  clean; `deps/verdi-raft` pin re-verified
  `a3375e867326a82225e724cc1a7b4758b029376f`. Fresh capped
  `lake env lean AxCheck.lean` printed verbatim `AxCheck sweep: 1985
  declarations across VerdiCompat modules, axiom set within
  [propext, Quot.sound]`; fresh capped `#print axioms` probe:
  `leaderLogs_preserved_invariant`, `allEntries_votesWithLog_invariant`,
  `allEntries_log_invariant` all
  `depends on axioms: [propext, Quot.sound]` verbatim; hatch grep
  (`sorry|native_decide|^axiom| axiom `) over LeaderLogsAssembly.lean:
  0 hits. All claims hold; building on them.
- 2026-08-23 [AGENT] UNIT-9 CLOSURE, re-derived fresh (`Require
  Import` walk @ a3375e8, pin re-verified; every imported Interface
  diffed against the INDEX's proved rows): exactly the six charter
  files, `wc -l` total **3,428** upstream lines; **no msg-ghost**
  (`grep -l "MsgRefinement\|GhostLog"` over all 12 closure files:
  empty). In-unit waves ([deps] = unported only):
  - W1: AllEntriesCandidateEntries 305 [—; CandidateEntries ✓,
    CroniesCorrect ✓, CroniesTerm ✓, AllEntriesTermSanity ✓] and
    appendEntriesRequest_term_sanity 48 [—; Sorted ✓];
  - W2: AllEntriesLeaderSublog 351 [AllEntriesCandidateEntries;
    VotesCorrect ✓, CroniesCorrect ✓, LeaderSublog ✓,
    OneLeaderPerTerm ✓];
  - W3: AllEntriesLogMatching 430 [AllEntriesLeaderSublog;
    LeaderSublog ✓, RLML ✓];
  - W4: PrefixWithinTerm 1,915 [AllEntriesLogMatching,
    AERTermSanity; LogsLeaderLogs ✓, RLML ✓, OneLeaderLogPerTerm ✓,
    LeaderLogsSorted ✓, LeaderLogsSublog ✓, LeaderSublog ✓,
    NextIndexSafety ✓, LeaderLogsContiguous ✓];
  - W5: LeaderCompleteness 379 [PrefixWithinTerm; LLTermSanity ✓,
    LeaderLogsPreserved ✓, EveryEntryWasCreated ✓,
    LeaderLogsVotesWithLog ✓, AllEntriesVotesWithLog ✓,
    VotesWithLogSorted ✓, TermsAndIndicesFromOne ✓,
    LeaderLogsLogMatching ✓].
  File plan: new `LeaderCompleteness.lean` (imports
  LeaderLogsAssembly), wired into VerdiCompat.lean from birth.
- 2026-08-23 Slice 50 (W1): `LeaderCompleteness.lean` opened —
  `append_entries_request_term_sanity`
  (AppendEntriesRequestTermSanityInterface.v:8-14 1:1; a one-line lift
  of base logs_sorted's packets_ge_prevTerm conjunct, exactly
  upstream's 48-line file) and **`allEntries_candidateEntries`**
  (AllEntriesCandidateEntriesInterface.v 1:1; upstream 305 lines) —
  unit 3's `*_preserves_candidateEntries` transports re-consumed for
  nine cases (the promotion-ledger payoff again); the two allEntries
  WRITERS: client_request's fresh record rides
  `won_election_cronies` on the pre-state leader ([AGENT] the
  head_term ghost lemma sharpened with the `st.2.type = .Leader`
  conjunct its fresh case always had — two consumer patterns updated),
  append_entries' fresh records ride the pre-state `CandidateEntries`
  nw half. [AGENT] Gotcha for successors: after editing a lemma in an
  IMPORTED module, `lake env lean <file>` type-checks against the
  STALE olean — the resulting rcases arity errors look like dependent-
  elimination failures; use `lake build <module>` so deps rebuild
  first. Build green, sweep 1998 (was 1985).
- 2026-08-23 Slice 51 (W2): `allEntries_leader_sublog`
  (AllEntriesLeaderSublogInterface.v:8-13 1:1; upstream 351 lines) —
  a leader's current-term record is in its log. New:
  `lifted_leader_sublog_nw` (9th lift_prop consumer),
  `handleAppendEntries_true_reply_type`/`_false_reply_state` (a true
  reply leaves a Follower; a false reply is a no-op — together giving
  upstream's `update_elections_data_appendEntries_log_allEntries_leader`:
  an AE that leaves you Leader was a rejection), head_term sharpened
  again with `e ∈ d.log`. The cases: CR's fresh record forces
  recorder = leader via `lifted_one_leader_per_term`; AE fresh records
  ride the lifted nw `leader_sublog`; an RVR that MINTS the leader dies
  on `wonElection_candidateEntries_rvr` against W1's
  `allEntries_candidateEntries` (its first payoff); all still-leader
  handlers are ct/log-preserving by their specs. [AGENT] subst-direction
  bookkeeping (three more instances — `leader = p.pDst` eliminates
  leader; `leader = h` kept leader here) resolved per-site by compile
  probe; recorded again: NEVER assume the direction, check the errors.
  Build green, sweep 2014.
- 2026-08-23 Slice 52 (W3, c4dc53e4): `allEntries_log_matching`
  (AllEntriesLogMatchingInterface.v:8-14 1:1; upstream 430 lines) —
  the host∧nw simultaneous induction
  (`allEntries_log_matching_inductive`): a generic transport
  (`almi_of_update`, parameterized by "sends no AppendEntries") covers
  six handlers; CR's fresh head-record quadrants close by the
  host/nw/allEntries `leader_sublog` lifts against the maxIndex+1
  index ([AGENT] head_term sharpened a third time, with the index
  conjunct — its fresh witness is the log head literal, so `rfl`);
  AE's quadrants ride `entries_match_nw_host` + uniqueIndices and the
  nw-IH; two-packet gluing is `almi_packets_entries_eq`
  (entries_match_nw_1 + contiguity); doLeader's fresh replicas reduce
  to the host IH via doLeader_messages. Also [AGENT]: the CR
  leader-append-without-record branch is refuted by a length argument
  on the ghost equation (the guard fires exactly on log growth) —
  upstream's combined log_allEntries lemma exposes this jointly;
  ours splits it. Four unit-9 AxCheck pins (fresh probe, all
  [propext, Quot.sound]). Build green, sweep 2029.
- 2026-08-23 Unit-9 gate (mid-unit, at the chartered split point):
  `GOLEAN_ALLOW_NO_DIFF=1 GOLEAN_MEM_MAX=24G scripts/ci` —
  **RESULT: PASS, exit 0** (log: `artifacts/ci-arc3-unit9.log`,
  gitignored; no-diff notes are the allowed docs+compat hatch).
  Comparator-landmark note now "56 theorems @ 1730567a2d3f, 75
  commit(s) ago" — same operator-merge-time flag as before; nothing
  touches a designated statement or Challenge's closure.

## Final entry — unit 9 SPLIT at the chartered point (2026-08-23, tip c4dc53e4 + this commit)

**Context-rule stop, per the coordinator's activation**: the four
feeder files (W1-W3) are COMPLETE and gate-green; PrefixWithinTerm
(1,915 upstream lines — the flagged strain point) and
LeaderCompleteness are the chartered remainder. A completed prefix +
chartered remainder is branch-complete.

**Proved at tip** — `LeaderCompleteness.lean` (1,426 lines, zero
sorry/native_decide; sweep-enforced: 2029 declarations within
[propext, Quot.sound], four new curated pins). `#print axioms`
verbatim (fresh capped probe):

```
'VerdiCompat.Raft.append_entries_request_term_sanity_invariant' depends on axioms: [propext, Quot.sound]
'VerdiCompat.Raft.allEntries_candidateEntries_invariant' depends on axioms: [propext, Quot.sound]
'VerdiCompat.Raft.allEntries_leader_sublog_invariant' depends on axioms: [propext, Quot.sound]
'VerdiCompat.Raft.allEntries_log_matching_invariant' depends on axioms: [propext, Quot.sound]
```

1,134 of the closure's 3,428 upstream lines ported (4 of 6 files);
71 commits on the lane (recomputed at c4dc53e4). The INVARIANT INDEX
above is current (60 data rows, recomputed: `grep -c "^| "` = 61
minus the header — verify at consumption).

**Honestly open (carried):** GAP-1 (never triggered), GAP-2
(msg-ghost; absent from this unit's closure — expected at the
state-machine-safety cap), GAP-4 (constructive discipline holding),
GAP-6 (leader_completeness proof — the remainder below).

**Next unit's charter (Arc 3, unit 10 — the unit-9 remainder;
RE-DERIVE the closure fresh, as always):**
- **`prefix_within_term`** (PrefixWithinTermInterface.v /
  PrefixWithinTermProof.v, 1,915 lines — the heavy one). Its deps are
  now ALL PORTED (verified at the unit-9 opening): LogsLeaderLogs,
  RLML, OneLeaderLogPerTerm, LeaderLogsSorted, LeaderLogsSublog,
  LeaderSublog, NextIndexSafety, LeaderLogsContiguous,
  AllEntriesLogMatching ✓, AERTermSanity ✓, AllEntriesLeaderSublog ✓.
- **`leader_completeness`'s PROOF** (LeaderCompletenessProof.v, 379
  lines), discharging the unit-4 statement — THE GAP-6 CLOSE. After
  it: the T3 ladder reads election safety ✓ (unit 2), log matching ✓
  (unit 6), leader completeness ✓; the remaining T3 head is
  state-machine safety (StateMachineSafetyProof.v + its closure —
  re-derive; msg-ghost EXPECTED there, minimal-port-on-first-need).
Successors re-verify this unit fresh: build + sweep 2029 + the
four-headliner probe above + hatch grep over LeaderCompleteness.lean.

## Unit 10 — LEADER COMPLETENESS (2026-08-23, coordinator-posted charter)

Charter: the unit-9 remainder — `prefix_within_term`
(PrefixWithinTermProof.v, 1,915 lines, the largest single file any
worker has taken; DAG derived and posted first, slice by the DAG) and
`leader_completeness`'s PROOF (LeaderCompletenessProof.v, 379 lines),
discharging the unit-4 statement. Split discipline available: a
completed prefix + chartered remainder is branch-complete.

- 2026-08-23 SUCCESSOR RE-VERIFICATION of unit 9 (recomputed, fresh
  reader): tip d5efc9e8, tree clean, branch `campaign-arc3`;
  `deps/verdi-raft` pin re-verified
  `a3375e867326a82225e724cc1a7b4758b029376f` (read from the MAIN
  checkout, as every unit). Fresh capped `lake build` (24G) green
  ("Build completed successfully (49 jobs)"); the sweep line there was
  a cache replay, so re-derived by fresh capped
  `lake env lean AxCheck.lean` — verbatim `AxCheck sweep: 2029
  declarations across VerdiCompat modules, axiom set within
  [propext, Quot.sound]`. Fresh capped `#print axioms` probe
  (repo-local scratch): `allEntries_log_matching_invariant`,
  `allEntries_leader_sublog_invariant`,
  `allEntries_candidateEntries_invariant` all
  `depends on axioms: [propext, Quot.sound]` verbatim. Hatch grep
  (`sorry|native_decide|^axiom| axiom `) over LeaderCompleteness.lean:
  0 hits (exit 1). All claims hold; building on them.
- 2026-08-23 [AGENT] UNIT-10 CLOSURE, re-derived fresh (`Require
  Import` walk @ a3375e8, pin re-verified by `git rev-parse`): exactly
  the two charter files, `wc -l` = 1,915 + 379 = **2,294** upstream
  lines. Every imported Interface diffed against the INVARIANT INDEX's
  proved rows — ALL ported (PWT needs: LogsLeaderLogs ✓, RLML ✓,
  OneLeaderLogPerTerm ✓, LeaderLogsSorted ✓, LeaderLogsSublog ✓,
  LeaderSublog ✓, NextIndexSafety ✓, LeaderLogsContiguous ✓,
  AllEntriesLogMatching ✓, AERTermSanity ✓, AllEntriesLeaderSublog ✓;
  LC needs: PWT (this unit), LLTermSanity ✓, LeaderLogsPreserved ✓,
  EveryEntryWasCreated ✓, LeaderLogsVotesWithLog ✓,
  AllEntriesVotesWithLog ✓, VotesWithLogSorted ✓,
  TermsAndIndicesFromOne ✓, LeaderLogsLogMatching ✓). **No msg-ghost**
  (`grep -l "MsgRefinement\|GhostLog"` over all 4 files: empty) —
  GAP-2 stays untouched.
- 2026-08-23 [AGENT] PWT INTERNAL LEMMA DAG (posted per charter,
  upstream lines @ a3375e8). The file has TWO STANDALONE summit
  theorems proved directly from ported invariants (not part of the
  induction), then a six-conjunct inductive invariant:
  - **T1 `log_log_prefix_within_term_invariant`** (:107-149,
    standalone): both hosts' entries resolve through
    `logs_leaderLogs_invariant`; `one_leaderLog_per_term_log`
    identifies the two snapshots; entries_contiguous + maxIndex_is_max
    produce an index-matched witness; `entries_match_invariant`
    transfers. Deps all ported.
  - **T2 `append_entries_append_entries_prefix_within_term_invariant`**
    (:154-747, standalone, the summit — ~590 lines): apply
    `logs_leaderLogs_nw_invariant` to BOTH packets,
    `one_leaderLog_per_term_log` identifies the snapshot, then a 3×3
    case grid over the two packets' prevLog disjunction pairs; entries
    cross via `entries_match_nw_1_invariant` or die on
    `Prefix_maxIndex` (✓ ported) / contiguity bounds. NEW support
    needed (CommonTheorems.v): `app_contiguous_maxIndex_le_eq` (:2032),
    `sorted_app_1` (:2049), `contiguous_app_prefix_contiguous` (:2096),
    `sorted_term_index_lt` (:2112), `contiguous_app_prefix_2` (:2125),
    `contiguous_0_app` (:2140).
  - **D** the conjunct defs: `append_entries_append_entries..._nw`
    (:95), the five others + `prefix_within_term_inductive` (:748-786;
    conjuncts: allEntries_leaderLogs, log_leaderLogs, allEntries_log,
    allEntries_AE_nw, AE_leaderLogs, AE_log).
  - **H** helpers: mostly ported under lane names (ghost
    leaderLogs/allEntries update lemmas, `handleAppendEntries_reply_
    entries`, `handleClientRequest_log_full`, doLeader message specs,
    `nextIndex_sanity` = LeaderLogsAssembly:308,
    `lifted_leader_sublog_host`/`_nw`). NEW:
    `findGtIndex_prefix_within_term` (:788),
    `prefix_within_term_union` (:902) / `_subset` (:1385);
    `removeAfterIndex_maxTerm_in` (:915) appears consumer-less
    downstream — port only on need.
  - **P1-P11** the eleven obligations: `_append_entries` (:928, the
    inductive centerpiece — T2 + `allEntries_log_matching_invariant` +
    `append_entries_request_term_sanity_invariant` +
    `entries_match_nw_host_invariant`); `_client_request` (:1158 —
    `leaderLogs_sublog_invariant`, `allEntries_leader_sublog_invariant`,
    lifted leader_sublog host+nw against maxIndex+1); `_do_leader`
    (:1394 — doLeader spec trichotomy, `nextIndex_sanity`,
    `sorted_term_index_lt`, T1 via `prefix_within_term_subset`);
    `_request_vote_reply` (:1539 — fresh snapshot = winner's log, T1
    closes the new leaderLog conjuncts); `_append_entries_reply`
    (:1588), `_timeout` (:1644), `_request_vote` (:1720),
    `_do_generic_server` (:1789): pure transports (no log/leaderLogs/
    allEntries/AE-packet changes); `_init` (:1844),
    `_state_same_packet_subset` (:1854), `_reboot` (:1863) boilerplate.
  - **A** `prefix_within_term_inductive_invariant` (:1890) via the
    ported `refined_raft_net_invariant`; interface fields =
    conjunct 1 + T1 (pwti instance :1909).
- 2026-08-23 [AGENT] LC DAG (LeaderCompletenessProof.v): `argmin` def
  already ported (CommonDefinitions.lean:65); NEW `argmin_None`/
  `argmin_elim` (CommonTheorems.v:958-997); the local
  `contradicting_leader_logs_on_leader`/`contradicting_leader_logs`
  fixpoints + `minimal_contradicting_leader_log` + ten small
  elim/complete lemmas (:33-196; entry DecidableEq ✓, nodes/allFin_all/
  allFin_NoDup ✓); `maxTerm/maxIndex_zero_or_entry` (:198-210);
  **`leader_completeness_directly_committed_invariant`** (:212-337 —
  minimal-contradicting-log descent: pwt conjunct 1 kills the
  same-term-lower-index escape, every_entry_was_created +
  leaderLogs_preserved kill the lower-term escape, then
  leaderLogs_votesWithLog's quorum × the directly-committed quorum
  pigeon-intersect and moreUpToDate + votesWithLog_sorted +
  terms_and_indices_from_one force the contradiction);
  **`leader_completeness_committed_invariant`** (:339-364 — directly
  committed + `leaderLogs_entries_match_invariant`);
  **`leader_completeness_invariant`** (:366-373) — THE GAP-6 CLOSE,
  discharging LeaderLogs.lean:3901's unit-4 statement. NOTE (checked):
  Properties.lean has NO LeaderCompleteness transfer target
  (StateMachineSafety/OneLeaderPerTerm/LogMatching only) — leader
  completeness is a ghost-layer (leaderLogs) statement with no base
  projection upstream either; nothing further owed there.
- 2026-08-23 [AGENT] Slice plan by the DAG (file: LeaderCompleteness
  .lean, continuing unit 9's): 53 = T2 support layer + T1;
  54 = T2; 55 = D defs + the eight transport obligations; 56 = CR +
  DL obligations; 57 = AE obligation; 58 = assembly + interface
  theorems + pins; 59 = LC scaffolding (argmin lemmas +
  contradicting layer); 60 = LC invariants + pins + INDEX + gate +
  final entry. Split point if the honest budget forces one: after 58
  (PWT complete = a branch-complete prefix; LC alone is a small
  successor unit).
- 2026-08-23 Slice 53 (added0b1): `prefix_within_term` def added to
  CommonDefinitions.lean (:108-114 1:1, closing that header's "still
  not ported" note), the two interface defs, the T2 support layer
  (sorted_app_1/_2, Prefix_maxIndex, app_contiguous_maxIndex_le_eq —
  in the sharper `l2 = []` form — contiguous_app_prefix_contiguous,
  contiguous_app_prefix_2, pwt union/subset/findGtIndex), and **T1
  `log_log_prefix_within_term_invariant`** (:107-149 1:1 route:
  logs_leaderLogs both sides, one_leaderLog_per_term_log identifies,
  contiguity witness, entries_match or uniqueIndices). [AGENT]
  `contiguous_0_app` NOT ported: the lane's `sorted_app_in_1` is the
  same fact modulo the positivity premise (supplied by contiguity at
  call sites). The omega-on-abbrev gotcha re-hit once (logIndex);
  explicit Nat lemmas per the record. Build green, sweep 2043.
- 2026-08-23 Slice 54: **T2
  `append_entries_append_entries_prefix_within_term_invariant`**
  (:154-747, the file's summit — upstream ~590 lines). [AGENT]
  PROOF-SHAPE CALL (logged; §9 guided re-proof — same lattice inputs,
  re-derived route): upstream's eight ~70-line bullets (3×3 disjunction
  grid, locked_or contortions) collapse to ONE extracted positioning
  lemma `aeae_e_in_ll` — under `e`'s logs_leaderLogs_nw decomposition,
  ANY witness `y ∈ ll` with `e.eIndex ≤ y.eIndex` forces `e ∈ ll`
  (own-term block sits above maxIndex ll via sorted_app_in_1 +
  Prefix_maxIndex_eq when the prefix is nonempty; the empty-prefix
  branches die on the packet's own prevLog disjunction) — plus a clean
  two-sided split on `pli' < e.eIndex`: transfer side = contiguity
  witness in es' → entries_match_nw_1 (same-term block) or
  uniqueIndices-in-ll (snapshot block); prevLog side = the three
  disjuncts answer directly (e2-in-ll case via positioning +
  sorted_index_term). ~170 Lean lines for the 590. Build green,
  sweep 2047.
- 2026-08-23 Slice 55: the six conjunct defs + `prefix_within_term_
  inductive` (:748-786 1:1), the generic transport `pwti_of_update`,
  and EIGHT obligations: init, timeout, request_vote,
  append_entries_reply, do_generic_server, state_same_packet_subset,
  reboot (all via the transport + the no-AE packet arguments), and
  request_vote_reply written out (leaderLogs growth: the fresh
  snapshot = the winner's own log via `leaderLogs_update_elections_
  data_RVR` + `handleRequestVoteReply_log`; conjuncts 1/5 re-route
  through IH's allEntries_log / append_entries_log, conjunct 2 is
  T1's first consumer — exactly upstream's :1539-1587 route). Build
  green, sweep 2067. Remaining obligations: client_request,
  do_leader, append_entries.
- 2026-08-23 Slice 56: the client_request + do_leader obligations
  (upstream :1158-1331, :1394-1516), each as an aux lemma over an
  ABSTRACT successor net + a thin wrapper. [AGENT] Gotcha recorded for
  successors: an obligation proved directly against the literal
  `⟨ps', st'⟩` net leaves goals with `{nwPackets := …}.nwState h0`
  projections that `rw` cannot match against `st' h0`-shaped equations
  (application/`exact` see through by defeq; `rw` is syntactic) — the
  aux-lemma-over-abstract-`net'` shape avoids the whole class; ALSO the
  var=var subst direction bit again exactly as recorded (by_cases
  `h0 = h` + subst eliminates `h`; flipped to `h = h0`), the
  omega-on-abbrev class twice (explicit Nat lemmas), and rw-on-a-
  literal-entry's projection (`⟨…⟩.eTerm` is defeq to its field — end
  the rw at the defeq point). CR route: fresh record/entry at
  maxIndex+1 forces term-mates into the leader's own log
  (leaderLogs_sublog / allEntries_leader_sublog / lifted host+nw
  leader_sublog) then dies on maxIndex_is_max — or the fresh object
  itself is the goal member. DL route: findGtIndex trichotomy against
  pli with findAtIndex witness (uniqueIndices / sorted_index_term) and
  the none∧pli≠0 corner dead on nextIndex_sanity; conjuncts 5/6 are
  prefix_within_term_subset over IH log_leaderLogs / T1. Build green,
  sweep 2075. Remaining: append_entries (:928-1142) — the last
  obligation.
- 2026-08-23 Slice 57: the append_entries obligation (:928-1142, the
  inductive centerpiece) as `pwti_append_entries_aux` + wrapper.
  [AGENT] The upstream case soup factors into TWO reusable cores:
  `hold_newlog` (an old RECORD against the spliced log — conj-4 IH
  classifies against the packet; the (pli,plt) case collapses through
  `allEntries_log_matching` onto the pivot; the below-pli case
  trichotomizes on the term with `append_entries_request_term_sanity`
  killing the low side) and `hnw_newlog` (an in-flight ENTRY against
  the spliced log — same shape with T2 in place of the conj-4 IH and
  `entries_match_nw_host` in place of allEntries_log_matching). Fresh
  records ARE the packet's entries, so their goals are membership in
  the freshly spliced log (or conj-6 IH when the log rejected). Conj 4
  fresh-record × other-packet is T2 verbatim — the standalone theorem's
  purpose. Reply is never an AE (`handleAppendEntries_reply_entries`).
- 2026-08-23 Slice 58: **`prefix_within_term_inductive_invariant`**
  (:1890) through the ported `refined_raft_net_invariant`, and the
  interface field `allEntries_leaderLogs_prefix_within_term_invariant`
  (:21-24; the other field is T1) — **prefix_within_term COMPLETE**,
  the 1,915-line file fully ported. Four AxCheck pins added (captured
  from a fresh capped probe — all [propext, Quot.sound]). Full build
  green, sweep 2081; hatch grep over LeaderCompleteness.lean: 0
  (exit 1); file now 2,927 lines. INDEX row updated.
- 2026-08-23 Slice 59: the LC scaffolding — `argmin_None`/`argmin_elim`
  (CommonTheorems.v:958-986; the argmin def was already ported),
  the `contradicting_leader_logs_on_leader`/`contradicting_leader_logs`
  fixpoints + `minimal_contradicting_leader_log` (:33-54) and the
  seven elim/complete lemmas (:56-196; the three per-element facts
  merged into one `_elim` pass), and `moreUpToDate_elim` — the Prop
  form via `Bool.or/and_eq_true` + `beq_iff_eq` + `Nat.ble_eq`,
  constructively (the LawfulBEq trap avoided per the lane record).
  [AGENT] Gotchas: `simp only [defname, hscrut] at h` is the reliable
  way to reduce an equation-compiled fixpoint under a known scrutinee
  (`rw [defname]` has no equation of that name; a bare rcases-then-rw
  leaves an unreduced match that `split at` mis-cases); and the
  injection-pair subst eliminated the RHS names again (log0 → log').
- 2026-08-23 Slice 60: **`leader_completeness_directly_committed_
  invariant`** (:212-337 — the minimal-contradicting-log descent,
  exactly upstream's route: the `hbelow` claim via pwt-conjunct-1 /
  every_entry_was_created + minimality + leaderLogs_preserved; then
  leaderLogs_votesWithLog's quorum pigeon-intersected with the
  directly-committed quorum via unit-3's constructive pigeon +
  div2_correct; the common voter's record forced into the vote log by
  allEntries_votesWithLog + minimality; moreUpToDate against the
  sorted vote log's maxTerm/maxIndex closes both branches, with
  terms_and_indices_from_one ruling out the empty snapshot),
  **`leader_completeness_committed_invariant`** (:339-364, via
  leaderLogs_entries_match), and **`leader_completeness_invariant`**
  (:366-373) — **GAP-6 CLOSED**: the unit-4 statement
  (LeaderLogs.lean `leader_completeness`) is discharged. Three AxCheck
  pins (fresh capped probe, all [propext, Quot.sound]). Full build
  green, sweep 2138; hatch grep 0 (exit 1); LeaderCompleteness.lean =
  3,356 lines. INDEX row: leader_completeness PROVED (T3).
- 2026-08-23 Unit-10 final gate: `GOLEAN_ALLOW_NO_DIFF=1
  GOLEAN_MEM_MAX=24G scripts/ci` — **RESULT: PASS, exit 0** (log:
  `artifacts/ci-arc3-unit10.log`, gitignored; the no-diff notes are the
  allowed docs+compat hatch — unit 10 touched only `compat/verdi/**` +
  this log). The report-only comparator-landmark note now reads
  "56 theorems @ 1730567a2d3f, 83 commit(s) ago" — same
  operator-merge-time flag as units 1-9; nothing in this unit touches a
  designated statement or Challenge's closure (statement-TCB step ok).

## Final entry — unit 10 complete (2026-08-23, tip 5632bbbd + this commit)

**Proved at tip — GAP-6 CLOSED: `leader_completeness`, and the whole
unit-9/10 closure with it.** Both charter files ported (2,294 upstream
lines: PrefixWithinTermProof.v 1,915 + LeaderCompletenessProof.v 379),
statements 1:1 with their Interface files @ a3375e8; zero
sorry/native_decide in campaign files (grep; sweep-enforced: 2138
declarations within [propext, Quot.sound], plus seven new curated
pins). `#print axioms` verbatim (fresh capped `lake env lean` probes
against the built package):

```
'VerdiCompat.Raft.log_log_prefix_within_term_invariant' depends on axioms: [propext, Quot.sound]
'VerdiCompat.Raft.append_entries_append_entries_prefix_within_term_invariant' depends on axioms: [propext, Quot.sound]
'VerdiCompat.Raft.prefix_within_term_inductive_invariant' depends on axioms: [propext, Quot.sound]
'VerdiCompat.Raft.allEntries_leaderLogs_prefix_within_term_invariant' depends on axioms: [propext, Quot.sound]
'VerdiCompat.Raft.leader_completeness_invariant' depends on axioms: [propext, Quot.sound]
'VerdiCompat.Raft.leader_completeness_directly_committed_invariant' depends on axioms: [propext, Quot.sound]
'VerdiCompat.Raft.leader_completeness_committed_invariant' depends on axioms: [propext, Quot.sound]
```

**THE T3 LADDER (constitution §2.3), stated plainly:**
- **Election safety ✓** (unit 2: `one_leader_per_term_invariant` +
  `oneLeaderPerTermStatement_holds`, base layer via lower_prop);
- **Log matching ✓** (unit 6: `log_matching_invariant` +
  `logMatchingStatement_holds`, base layer);
- **Leader completeness ✓** (THIS UNIT:
  `leader_completeness_invariant`, refined/ghost layer — upstream has
  no base-layer projection of it and Properties.lean declares no
  LeaderCompleteness transfer target (checked; only
  StateMachineSafety/OneLeaderPerTerm/LogMatching), so the ghost-layer
  theorem IS the landing point, exactly as in verdi-raft);
- remaining T3 head: **state-machine safety** (unit 11's charter
  below). Per §2.3 these are HEADLINE-AS-PROVED candidates —
  designation is Mike's act, not the campaign's; nothing was
  designated here.

Inventory: `LeaderCompleteness.lean` (3,356 lines; the unit-9 feeders
at its head). Unit-10 additions: the pwt vocabulary + T2 support layer
(sorted_app_1/_2, Prefix_maxIndex, app_contiguous_maxIndex_le_eq,
contiguous_app_prefix_contiguous/_2, pwt union/subset/findGtIndex);
**T1 `log_log_prefix_within_term_invariant`**; **T2 (the AE×AE
cross-packet fact)** via the extracted positioning lemma
`aeae_e_in_ll` (~170 lines for upstream's ~590); the six-conjunct
`prefix_within_term_inductive` + all eleven obligations
(`pwti_of_update` transport; CR/DL/AE as aux-over-abstract-net lemmas;
AE's two cores `hold_newlog`/`hnw_newlog`);
`prefix_within_term_inductive_invariant` + both interface fields; the
argmin/contradicting-leader-logs layer + `moreUpToDate_elim`
(constructive, LawfulBEq-free); and the three leader_completeness
theorems. `prefix_within_term` def added to CommonDefinitions.lean
(:108-114, closing its header's recorded gap). The INVARIANT INDEX
above is current (60 data rows, recomputed: `grep -c "^| "` = 61 minus
the header). 79 commits on the lane (`git log f64d9b21..HEAD --oneline
| wc -l`, recomputed at 5632bbbd).

**Honestly open (carried; none counted toward any total):**
- GAP-1 (primed variants): STILL never triggered — no unit-10 proof
  needed one; carried as port-on-first-need.
- GAP-2 (msg-ghost): NOT in unit 10's closure (grep at unit start:
  empty) — but CONFIRMED at the state-machine-safety cap:
  `StateMachineSafetyProof.v` imports `RaftMsgRefinementInterface` +
  the three GhostLog* interfaces (read at a3375e8, unit-11 preview).
  The minimal-port-on-first-need clause WILL fire next unit.
- GAP-4 (classical-list doctrine): carried; unit 10 resolved every
  instance constructively (moreUpToDate_elim, the eraseOne-style
  pigeon reuse).

**Next unit's charter (Arc 3, unit 11 — proposal; RE-DERIVE the
closure fresh before proving, as always):** the STATE-MACHINE-SAFETY
cap — the last T3 head. Preview at a3375e8 (verify fresh):
`StateMachineSafetyProof.v` (3,199 lines) +
`StateMachineSafetyPrimeProof.v` (518) sit on the msg-ghost layer
(GAP-2: `RaftMsgRefinementInterface`, GhostLogCorrect,
GhostLogsLogProperties, GhostLogLogMatching) plus a ring of unported
plain interfaces (CommitRecordedCommitted, MaxIndexSanity,
PrevLogLeaderSublog, LastAppliedLeCommitIndex, MatchIndexAllEntries,
TransitiveCommit, TermsAndIndicesFromOneLog(✓ base already),
plus ✓-rows). Expect multiple units; scope to the largest
self-contained prefix per the standing discipline, msg-ghost
minimal-port-on-first-need (design-doc §5 D1's generic-lift decision
point arrives here: the second ghost instance). Successors re-verify
THIS unit fresh: capped build + sweep 2138 + the seven-headliner probe
above + hatch grep over LeaderCompleteness.lean (expect 0).

## Unit 11 — the msg-ghost foundation (2026-08-23, coordinator-accepted charter)

Charter: the state-machine-safety cap, GAP-2 firing first — port the
minimal msg-ghost principle 1:1 (vocabulary, obligation shapes,
principle, transfer, §3.3 discharge witness) as its own gated slice
before any SMS invariant consumes it; context rule ACTIVE (the
msg-ghost principle alone is an acceptable unit-11).

- 2026-08-23 SUCCESSOR RE-VERIFICATION of unit 10 (recomputed, same
  worker continuing under the unit-11 charter): tip d7e3cfc8, tree
  clean; `deps/verdi-raft` pin re-verified
  `a3375e867326a82225e724cc1a7b4758b029376f`. Fresh capped
  `lake build` green; fresh capped `lake env lean AxCheck.lean`
  verbatim `AxCheck sweep: 2138 declarations across VerdiCompat
  modules, axiom set within [propext, Quot.sound]`; fresh
  seven-headliner `#print axioms` probe (log_log / T2 / inductive /
  allEntries_leaderLogs pwt + the three leader_completeness theorems):
  all `[propext, Quot.sound]` verbatim; hatch grep over
  LeaderCompleteness.lean: 0 (exit 1). All claims hold.
- 2026-08-23 [AGENT] UNIT-11+ CLOSURE, re-derived fresh (scripted
  transitive `Require Import` walk @ a3375e8, pin re-verified; diffed
  against the INDEX's proved rows): **20 unported proof files, 9,612
  upstream lines** (wc at the pin). Two charter names have NO proof
  files: CommitRecordedCommitted and MaxIndexSanity are proved INSIDE
  StateMachineSafetyProof.v (lifted forms) — deliverables of the cap,
  not separate units. Waves ([deps] = unported only):
  - W-A (GAP-2): RaftMsgRefinement 954 [—];
  - W-B (plain leaves, deps all ported): AllEntriesLeaderLogs 106,
    InLogInAllEntries 175, LogAllEntries 269, LastAppliedLeCommitIndex
    223, MatchIndexSanity 254, NoAppendEntriesToSelf 148,
    PrevLogCandidateEntriesTerm 489, TransitiveCommit 31;
  - W-C: NoAppendEntriesRepliesToSelf 155 + NoAppendEntriesToLeader
    111 [NoAEToSelf], PrevLogLeaderSublog 378 [PLCET],
    GhostLogCorrect 275 + GhostLogsLogProperties 201 [RaftMsgRef],
    GhostLogAllEntries 282 [RaftMsgRef, InLogInAllEntries],
    StateMachineSafetyPrime 518 [AllEntriesLeaderLogs];
  - W-D: MatchIndexLeader 146 [NoAERepliesToSelf],
    GhostLogLogMatching 564 [the ghost chain];
  - W-E: MatchIndexAllEntries 1,134 [NoAEToLeader, NoAEToSelf,
    LogAllEntries, MatchIndexLeader, MatchIndexSanity];
  - W-F: StateMachineSafety 3,199 [everything above].
- 2026-08-23 [AGENT] UNIT-11 SCOPE (minimal-port-on-first-need, the
  coordinator's sanctioned minimum): the msg-ghost FOUNDATION —
  `RaftMsgRefinementInterface.v` vocabulary (ghost_log,
  write_ghost_log, add_ghost_msg, the msg-refined params triple,
  `msg_refined_raft_intermediate_reachable`), the ELEVEN obligation
  shapes 1:1 (:83-195), the dispatchers, **THE principle
  `msg_refined_raft_net_invariant`** (Proof.v:58-275), the erasure
  half of the transfer (`mgv_deghost`, `msg_simulation_1`
  (Proof.v:566-645), `msg_lift_prop`, `msg_deghost_spec`), and a §3.3
  discharge witness. DEFERRED with consumer census (logged, not
  silent): (a) the PRIMED obligation set + `msg_refined_raft_net_
  invariant'` (Interface :197-439, Proof :276-565) — GAP-1's msg-side
  instance; consumers: exactly ONE use each in GhostLogsLogProperties/
  GhostLogAllEntries/GhostLogLogMatching/SMS (grep at the pin), each a
  candidate for the slice-39 pre-state route, decided at consumption;
  (b) `simulation_2`/`msg_lower_prop`(+`_all_the_way`) (Proof
  :655-940) — reghosting via msg-level dup-drop (needs a msg-level
  `subset_reachable` mirroring unit 7's); consumers: SMS only
  (3× msg_lower_prop, 1× lift_all_the_way). Both are the W-F unit's
  first work. Design note §5 D1's generic-lift decision: the msg-ghost
  is a DIFFERENT construction from the state-ghost (per-packet vs
  per-node), so the generic GhostSimulations lift still has one
  consumer per shape — inlined at the raft instance again, D1 stands.
- 2026-08-23 [AGENT] Witness choice (§3.3): `ghost_entries_gt_0` —
  every entry of every in-flight ghost log has a positive index. Real
  content (consumes every obligation's packet clause and handler log
  shape; rides msg_simulation_1 + the deghost-state equality into the
  existing refined entries_gt_0/log-shape lemmas), deliberately NOT
  one of the GhostLog* chain's named statements (no pre-emption,
  exactly unit 1's VotesShape discipline).
- 2026-08-23 Slice 62 (427c9262): `MsgRefinement.lean` opened — the
  ghost vocabulary (`ghost_log`, `write_ghost_log`, `add_ghost_msg` +
  app/log_eq lemmas), the mgv params triple (GhostSimulations.v
  :298-357 inlined at the raft instance, D1 again), and the
  five-constructor `msg_refined_raft_intermediate_reachable`
  (Interface :34-79). Wired into VerdiCompat.lean from birth.
- 2026-08-23 Slice 63: the ELEVEN obligation shapes (:83-195 1:1),
  the two dispatchers, and **THE principle
  `msg_refined_raft_net_invariant`** (Proof.v:58-275), re-proved in
  the sibling layer's assert-chain style. [AGENT] The genuinely new
  step vs unit 1: GHOST RECONCILIATION — the real handler attaches the
  FINAL state's log to all sends while the staged constructors attach
  each stage's; equal because doLeader/doGenericServer never move the
  log (`add_ghost_msg_log_eq` + doLeader_spec/doGenericServer_spec log
  equations, applied inside the final packet-coverage step). [AGENT]
  Gotcha for successors: the sibling's INLINED doLeader/doGenericServer
  constructor premise style (`(net.nwState h).1` in the sends) breaks
  at the msg layer — `update_same` is NOT definitional (if-blocked on
  a variable key), so the ghost argument can't reduce; upstream's
  explicit `nwState net h = (gd, d)` equation shape is the right port
  (adopted; the sibling got away with it only because ITS sends carry
  no state).
- 2026-08-23 Slice 64: the erasure half — `mgv_deghost_packet`/
  `mgv_deghost` (state untouched, only the wire loses its ghost — so
  `msg_deghost_spec` is `rfl` and every state equation in
  `mgv_ghost_simulation_1` is trivial where unit 1 needed
  `update_snd`), `mgv_deghost_send_packets` (the ghost-attachment
  collapse), `mgv_ghost_simulation_1` (all seven step_failure legs),
  **`msg_simulation_1`** (Proof.v:566-645), `msg_lift_prop` and
  `msg_lift_prop_all_the_way` (composing with unit 1's `lift_prop`).
- 2026-08-23 Slice 65: the §3.3 witness —
  **`ghost_entries_gt_0_invariant`**: every in-flight ghost log's
  entries have positive indices, through THE principle with ALL ELEVEN
  obligations discharged (fresh ghosts = the writing state's log via
  `ghost_of_send`; per-handler log shapes: CR's cons at maxIndex+1,
  AE's scratch/splice against the packet's entries via the msg-lifted
  `entries_gt_0_nw`, everything else log-preserving; the host-log
  positivity imported through `msg_simulation_1` — the transfer's
  first consumer). Five AxCheck pins (fresh capped probe, all
  [propext, Quot.sound]; the stale-olean gotcha re-hit at the probe —
  full `lake build` before `lake env lean`, per the unit-9 record).
  Build green, sweep 2213; hatch grep over MsgRefinement.lean: 0
  (exit 1); file = 1,133 lines.
- 2026-08-23 Unit-11 final gate: `GOLEAN_ALLOW_NO_DIFF=1
  GOLEAN_MEM_MAX=24G scripts/ci` — **RESULT: PASS, exit 0** (log:
  `artifacts/ci-arc3-unit11.log`, gitignored; no-diff notes are the
  allowed docs+compat hatch — unit 11 touched only `compat/verdi/**` +
  this log). The report-only comparator-landmark note now reads
  "56 theorems @ 1730567a2d3f, 89 commit(s) ago" — same
  operator-merge-time flag as units 1-10; nothing here touches a
  designated statement or Challenge's closure (statement-TCB step ok).

## Final entry — unit 11 complete (2026-08-23, tip 470c50f7 + this commit)

**Proved at tip — GAP-2's msg-ghost FOUNDATION.** The coordinator's
sanctioned minimal unit: the RaftMsgRefinement layer's vocabulary,
params, reachable, all eleven obligation shapes, THE principle, the
erasure half of the transfer, and the §3.3 discharge witness — 1:1
against `RaftMsgRefinementInterface.v` /
`RaftProofs/RaftMsgRefinementProof.v:12-275,566-654` @ a3375e8. Zero
sorry/native_decide (grep; sweep-enforced: 2213 declarations within
[propext, Quot.sound], plus five new curated pins). `#print axioms`
verbatim (fresh capped probe after full build — the stale-olean rule):

```
'VerdiCompat.Raft.msg_refined_raft_net_invariant' depends on axioms: [propext, Quot.sound]
'VerdiCompat.Raft.msg_simulation_1' depends on axioms: [propext, Quot.sound]
'VerdiCompat.Raft.msg_lift_prop' depends on axioms: [propext, Quot.sound]
'VerdiCompat.Raft.msg_lift_prop_all_the_way' depends on axioms: [propext, Quot.sound]
'VerdiCompat.Raft.msg_deghost_spec' depends on axioms: [propext, Quot.sound]
'VerdiCompat.Raft.ghost_entries_gt_0_invariant' depends on axioms: [propext, Quot.sound]
```

Inventory: `MsgRefinement.lean` (1,133 lines) — ghost vocabulary +
`add_ghost_msg_app`/`_log_eq`; the mgv params triple; the
five-constructor MRRIR; eleven obligations; dispatchers; **THE
principle** (with the ghost-stage reconciliation);
`mgv_deghost`/`mgv_ghost_simulation_1`/**`msg_simulation_1`**/
`msg_lift_prop`(+`_all_the_way`)/`msg_deghost_spec`; witness
**`ghost_entries_gt_0_invariant`** (all eleven obligations
discharged). The INVARIANT INDEX is current (61 data rows, recomputed
by line span :370-:430; `grep -c "^| "` = 63 counts additionally the
header and one wrapped prose line in the unit-10 final entry —
verified, not hand-waved). 85 commits on the lane (recomputed at
470c50f7).

**Honestly open (carried + new; none counted):**
- GAP-1 (primed variants): now has a MSG-side instance too — the
  primed msg obligation set + `msg_refined_raft_net_invariant'`
  (Interface :197-439, Proof :276-565) deferred with its census
  (ONE use each in GhostLogsLogProperties/GhostLogAllEntries/
  GhostLogLogMatching/SMS; each a slice-39-style pre-state candidate,
  decided at consumption).
- GAP-8 (new): the reghosting direction — `simulation_2`/
  `msg_lower_prop`/`msg_lower_prop_all_the_way` (Proof :655-940;
  needs a msg-level `subset_reachable` mirroring unit 7's) — deferred
  to the W-F cap unit, its only consumer (SMS: 3× msg_lower_prop).
- GAP-2 is CLOSED as chartered (the principle + erasure transfer are
  what the GhostLog* chain consumes); GAP-4 discipline held (no new
  classical dependencies).

**Next unit's charter (Arc 3, unit 12 — proposal; RE-DERIVE the
closure fresh, as always):** the W-B plain leaves + the first ghost
chain files, by the unit-11 wave table: `AllEntriesLeaderLogs` (106),
`InLogInAllEntries` (175), `LogAllEntries` (269),
`LastAppliedLeCommitIndex` (223), `MatchIndexSanity` (254),
`NoAppendEntriesToSelf` (148), `TransitiveCommit` (31),
`PrevLogCandidateEntriesTerm` (489) — then as budget allows W-C's
`GhostLogCorrect` (275) + `GhostLogsLogProperties` (201) (msg layer's
first real consumers; their single primed-principle uses decided
per-site). Successors re-verify THIS unit fresh: capped full build +
sweep 2213 + the six-headliner probe above + hatch grep over
MsgRefinement.lean (expect 0).

## Unit 12 — the W-B plain leaves (2026-08-23, coordinator-accepted charter)

Charter: the eight W-B files (~1,695 lines), then W-C's
GhostLogCorrect + GhostLogsLogProperties as the honest budget allows;
context rule ACTIVE — W-B alone is a complete unit.

- 2026-08-23 SUCCESSOR RE-VERIFICATION of unit 11 (recomputed, same
  worker continuing): tip 24dbbf97, tree clean; pin re-verified
  `a3375e867326a82225e724cc1a7b4758b029376f`; fresh capped
  `lake env lean AxCheck.lean` verbatim `AxCheck sweep: 2213
  declarations across VerdiCompat modules, axiom set within
  [propext, Quot.sound]`; fresh six-headliner probe (principle,
  simulation_1, lift, lift_all_the_way, deghost_spec, witness) all
  `[propext, Quot.sound]` verbatim; hatch grep over
  MsgRefinement.lean: 0 (exit 1). All claims hold.
- 2026-08-23 [AGENT] W-B CLOSURE re-checked fresh (imports of all 8
  proof files @ a3375e8): every imported Interface is an INDEX PROVED
  row — AERLeaderLogs/OneLeaderLogPerTerm/LeaderLogsSorted/RLML/
  AECameFromLeaders/AllEntriesLog/LeaderSublog/LHLLStrong (AELL);
  TermSanity (LogAllEntries); AEReplySublog+Sorted (MatchIndexSanity);
  LeaderCompleteness+RLML (TransitiveCommit — unit 10's theorem is
  its dep); CroniesTerm/CroniesCorrect/CandidateEntries (PLCET). NO
  hidden edges, NO msg-ghost. File plan: one new `SafetyLeaves.lean`
  (imports MsgRefinement), wired from birth.
- 2026-08-23 Slice 66 (8399c908): `SafetyLeaves.lean` opened — the two
  JOINT log/allEntries movement lemmas ported on first need
  (`update_elections_data_client_request_log_allEntries`
  (RefinementSpecLemmas.v:312-360, compact form) and
  `..._appendEntries_log_allEntries` (:404-441) with the new
  `handleAppendEntries_true_reply_currentTerm` — the correlation the
  lane's SEPARATE cases lemmas lose, exactly the split unit 9
  flagged); `transitive_commit_invariant` (committed is downward
  closed along entries_match — unit 10's `committed` def consumed);
  the FOUR-conjunct `all_entries_leader_logs` assembly (lwme =
  allEntries_log projection; exists_leaderLog = came_from_leaders;
  leaderLog_not_in via AERLeaderLogs' split + prefix_contiguous +
  one_leaderLog_per_term; leaderLogs_leader = LHLLStrong's weak face);
  and `in_log_in_all_entries_invariant` (the joint lemmas' first
  payoff). [AGENT] The full recorded gotcha set re-hit in ONE slice:
  nomatch-on-Bool-eq (cases + try-cases-with-done shape), subst
  direction ×2, literal-net rw (replace/show defeq bridging), rw
  auto-rfl not closing `≤` (explicit Nat.le_refl).
- 2026-08-23 Slice 67 (40c8e90d): `log_all_entries_invariant` — the
  term-aware twin: fresh CR/AE records land at their own terms (the
  joint lemmas' term components), old current-term entries ride
  `nepct_host_lifted` (lift_prop of base term-sanity) + Nat.le_antisymm
  against the handlers' monotone terms (`lae_of_update` transport
  with a term-only-grows premise; the strictly-grown case is vacuous
  by term sanity).
- 2026-08-23 Slice 68 (66b21957): the BASE pair —
  `lastApplied_le_commitIndex_invariant` (new watermark movement
  lemmas: advanceCurrentTerm/handlers keep la and never lower ci;
  `le_foldl_max` for advanceCommitIndex; doGenericServer's la jumps
  at most to ci) and `no_append_entries_to_self_invariant`
  (`doLeader_messages_not_self` reads the fan-out filter; every other
  send is a non-AE reply or nothing). [AGENT] doLeader unfolding needs
  the exact `unfold doLeader advanceCommitIndex; simp only []` 
  incantation before `repeat' split` (the `have`-bindings block bare
  split) — recorded; it is the lane's own doLeader_messages shape.
- 2026-08-23 [AGENT] SPLIT AT THE CLEAN BOUNDARY (context rule,
  coordinator-activated): a first draft of `match_index_sanity`
  surfaced rising error rate (guessed signatures, placeholder hatches
  that the sweep would rightly reject) — the draft was REVERTED
  uncommitted, per the split discipline; six of eight W-B files are
  landed and gate-green; `match_index_sanity` + 
  `prevLog_candidateEntriesTerm` are the chartered unit-13 remainder
  (with the partial recon recorded here: handleAppendEntriesReply/
  handleRequestVoteReply matchIndex case lemmas 1:1 from
  MatchIndexSanityProof.v:88-105/:148-161; applyEntries_matchIndex by
  the applyEntries_nextIndex induction pattern; the AER max-slot case
  rides append_entries_reply_sublog + maxIndex_is_max exactly as
  upstream; PLCET = candidateEntriesTerm (the term-level twin of
  candidateEntries, same shape modulo e.eTerm ↦ t) + eight preserves
  lemmas mirroring unit 3's + the doLeader creation case via
  candidate_entries_invariant on the findAtIndex pivot).
- 2026-08-23 Six AxCheck pins added for the unit-12 headliners
  (captured from a fresh capped probe — all [propext, Quot.sound]).
  Build green, sweep 2287 + pins; hatch grep over SafetyLeaves.lean: 0
  (exit 1); file = 1,082 lines.
- 2026-08-23 Unit-12 final gate: `GOLEAN_ALLOW_NO_DIFF=1
  GOLEAN_MEM_MAX=24G scripts/ci` — **RESULT: PASS, exit 0** (log:
  `artifacts/ci-arc3-unit12.log`, gitignored; no-diff notes are the
  allowed docs+compat hatch — unit 12 touched only `compat/verdi/**` +
  this log). Comparator-landmark note now "56 theorems @ 1730567a2d3f,
  94 commit(s) ago" — same operator-merge-time flag as units 1-11;
  nothing touches a designated statement or Challenge's closure
  (statement-TCB step ok).

## Final entry — unit 12 SPLIT at the clean boundary (2026-08-23, tip 0e62ce46 + this commit)

**Context-rule stop, per the coordinator's activation**: SIX of the
eight W-B files are COMPLETE and gate-green (1,175 of the wave's
~1,695 upstream lines); `match_index_sanity` (254L) and
`prevLog_candidateEntriesTerm` (489L) are the chartered remainder —
the draft of the former was REVERTED uncommitted when the error rate
rose (the split discipline: a completed prefix + a chartered
remainder is branch-complete; no hatch ever committed).

**Proved at tip** — `SafetyLeaves.lean` (1,082 lines, zero
sorry/native_decide; sweep-enforced: 2287 declarations within
[propext, Quot.sound], six new curated pins). `#print axioms` verbatim
(fresh capped probe):

```
'VerdiCompat.Raft.transitive_commit_invariant' depends on axioms: [propext, Quot.sound]
'VerdiCompat.Raft.all_entries_leader_logs_invariant' depends on axioms: [propext, Quot.sound]
'VerdiCompat.Raft.in_log_in_all_entries_invariant' depends on axioms: [propext, Quot.sound]
'VerdiCompat.Raft.log_all_entries_invariant' depends on axioms: [propext, Quot.sound]
'VerdiCompat.Raft.lastApplied_le_commitIndex_invariant' depends on axioms: [propext, Quot.sound]
'VerdiCompat.Raft.no_append_entries_to_self_invariant' depends on axioms: [propext, Quot.sound]
```

The INVARIANT INDEX is current (69 data rows, recomputed by table span
:370-:438 — this entry's first draft said 70, corrected against the
span; the two UNIT-13 CHARTER rows included). 90 commits on the
lane (`git log f64d9b21..HEAD --oneline | wc -l`, recomputed at
0e62ce46).

**Honestly open (carried):** GAP-1 (incl. the msg-side primed set with
its census), GAP-4 (constructive discipline holding), GAP-8
(msg reghosting — W-F's first work); the unit-13 remainder below.

**Next unit's charter (Arc 3, unit 13 — the unit-12 remainder + W-C;
RE-DERIVE closures fresh, as always):**
1. **`match_index_sanity`** (MatchIndexSanityProof.v, 254L, BASE) —
   the slice-69 recon is recorded in the split entry above (case
   lemmas :88-105/:148-161, applyEntries_matchIndex induction, the
   AER max-slot case via append_entries_reply_sublog).
2. **`prevLog_candidateEntriesTerm`** (PLCETProof.v, 489L) —
   `candidateEntriesTerm` (the term-level candidateEntries twin) +
   eight preserves lemmas (mirror unit 3's entry-level proofs) + the
   doLeader creation case via `candidate_entries_invariant` on the
   findAtIndex pivot entry.
3. Then W-C as budget allows: `GhostLogCorrect` (275L) +
   `GhostLogsLogProperties` (201L) — the msg-ghost principle's first
   real consumers (their single primed-principle uses decided per-site,
   slice-39 pre-state route first).
Successors re-verify THIS unit fresh: capped full build + sweep 2287 +
the six-headliner probe above + hatch grep over SafetyLeaves.lean
(expect 0).
