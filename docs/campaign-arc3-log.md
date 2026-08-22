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
| leader_completeness | STATEMENT ONLY (defs 1:1; proof = later unit) | Raft/LeaderCompletenessInterface.v:9-42 | LeaderLogs.lean (directly_committed/committed/leader_completeness defs) |
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

