# Campaign lane `campaign-arc4b` — SC1, the scope-risk front-load unit

Scoping-lane log. Branch `campaign-arc4b` @ base `3bbb0f10` (the
arc-4 lane's U18 gate tip), one writer, NEW FILES ONLY (hard rule:
no existing tracked file edited — this lane lands at a wave boundary
without textual conflict). Charter: three probes in priority order —
(1) the S2/S3 route question, (2) the native-S1 sizing probe, (3) the
harvest-granularity question — MEASUREMENTS AND DECISION INPUTS, not
machinery. Design of record: the campaign worktree's
`docs/2026-08-25_campaign-layerc-design.md` (v2; §8 D1–D3), with the
MID-UNIT RE-TARGET (coordinator, from a user design discussion,
2026-08-26): deliverables 1(d) and 2 re-framed around **the family
route b′** — the obligation SIGNATURE as the organizing frame (§8 D2
REVISED, re-read after the re-target; SC1 is named there as the
empirical gate: "whether arc-3's ported proofs factor through the
obligations or unfold concrete handlers — PORTS/ADAPTS/NEW decides
b′'s real cost").

New tracked files this unit (nothing else touched):
- `proofs/GoLeanProofs/Specs/Raft/NativeObligations.lean` — the
  obligation-signature draft (S1 fragment) + native
  `one_leader_per_term` + superstructure skeleton + 3 proved
  calibration links;
- `proofs/GoLeanProofs/Specs/Raft/NativeS23Route.lean` — the S2/S3
  checker census, needed invariants, commit-axis obligations, the
  leading route's statement chain + 4 proved leaf/demonstrator
  lemmas;
- this log.
Probes (gitignored): `artifacts/probe/ChoiceSiteProbe.lean` (the
site-labeled choice census), `artifacts/probe/AxNative.lean` (axioms
readout); artifacts `artifacts/choicesite-events.tsv`,
`artifacts/arc4b-proofs-build.log`.

## SC1 entry — 2026-08-26

- 2026-08-26 Slice 0 — LAUNCH VERIFICATION: `git status` clean at
  `3bbb0f10`; 89G free at launch (≥ the 40G floor; every build this
  unit `GOLEAN_MEM_MAX=48G scripts/capped`, staggered behind
  `free -g` checks — the arc-4 worker builds concurrently and this
  lane yields). Cold worktree (no `.lake`): full proofs+Audit build
  from scratch, capped — green (530 jobs at this tip;
  `artifacts/arc4b-proofs-build.log`). deps/ pre-bootstrapped with
  the ci default set (go/goose/iris-lean/perennial/raft).
  [AGENT] read-first per charter: layer-C design v2 §8 (re-read after
  the re-target), arc-4 log U18 entry + C1 verdict block, seam note
  §4c, T3 lattice sources (read-only), the C1 adapter probe
  (`campaign-arc4/artifacts/probe/A4AdapterProbe.lean`, read-only).

### Slice 1 — THE S2/S3 ROUTE QUESTION (charter 1, re-framed b′)

**(1a) The checker census — S2/S3 exactly** (subject source, all
line-cited at this tip):

- The S2/S3 span is `tools/raftsubject/twin-lib.go` `apply`
  (298–335), called per committed entry from `harvest`'s apply loop
  (289–291). S3 monotonicity (302–312): PER NODE, `idx > nd.applied`
  (strict index increase) ∧ `trm ≥ nd.lastTrm` (non-decreasing
  term) over the apply sequence, on (e.Index, e.Term). S3 anomaly
  (313–317): `e.Type == EntryNormal` else violation. S2 agreement
  (325–334): CROSS-NODE, non-empty EntryNormal entries only (319–321
  skips the leader noop): global `byIndex : index ↦ (term, data,
  node)`; a later apply at a recorded index must equal `(term, data)`.
  Fields consumed: Index/Term/Data/Type of applied entries — nothing
  else. The U18 census already established the span is small
  (`apply` 324–463 steps ×9; never the balloon).

**(1b) The precise abstract invariants each false-delta needs** (over
specRound traces; stated as Props in `NativeS23Route.lean` §2):

- S2 ⇐ `state_machine_safety_host` restricted to non-empty normal
  entries — any two applied entries at one index agree on
  (term, data). **T3 fact that re-prices every route: this statement
  is STATEMENT-ONLY in the tree** (`VerdiCompat/Properties.lean:83`;
  `LeaderLogs.lean:31-33` records `leader_completeness` as "defs
  only; its proof is a later arc's"; the proved lattice tops out at
  `one_leaderLog_per_term`). There is NO lattice SMS/log-matching
  proof to port, project, or transfer — every S2 route builds the
  superstructure fresh.
- S3-index ⇐ a LOCAL Ready-machinery fact (not a distributed
  invariant): `nextCommittedEnts` returns the (applying,
  maxAppliable] slice in log order (raftsubject/raft/log.go:220-244)
  and `appliedTo` enforces prevApplied ≤ i ≤ committed (log.go:
  332-336).
- S3-term ⇐ per-node log term-monotonicity + S3-index +
  applied-from-log.
- S3-anomaly ⇐ entry provenance (all entries EntryNormal: driver
  proposals + the noop, raft.go:980-81).

**(1c) The commit-axis check — against the SIGNATURE (per the
re-target): VERIFIED at the statement level.** The S2/S3-needed
invariants consume the commit axis ONLY through three obligation
members (stated as Props with dischargers in `NativeS23Route.lean`):

- O-C1 `commitInWindow` — never decrease, never past log end (etcd:
  the `commitTo` guard, log.go:322-330);
- O-C2 `leaderCommitOk` — leader commits only to a quorum-certified
  own-term index (etcd: `maybeCommit` raft.go:794-98 →
  `raftLog.maybeCommit` log.go:455-462 `matchTerm` guard +
  `trk.Committed()`; Verdi: the advanceCommitIndex quorum rule);
- O-C3 `followerCommitOk` — follower commit bounded by
  max(old, min(leaderCommit, matchedPrefix)).

**The A4 kill-point DISSOLVES at the obligation level — proved, both
halves** (`NativeS23Route.lean`): `etcd_emptyAccept_discharges`
(etcd's commit-advance-without-new-entries, log.go:129, sits at the
envelope's SUPREMUM) and `verdi_frozen_discharges` (Verdi's frozen
commit, the C1 probe's `verdi_emptyAE_commit_frozen`, sits at the
INFIMUM) — the same `followerCommitOk` obligation, visibly different
implementations: the vacuity-discipline demonstrator, and the b′
resolution of the C1 A4 mismatch (which was real only against
Verdi's POINT rule, never against the family envelope). ONE caveat,
named and bounded: etcd's heartbeat commit (raft.go:1854-55,
locally unguarded `commitTo(m.Commit)`) discharges O-C3 only through
the leader's send-side bound (min(match[to], committed)), which
would need a leader match-soundness signature member — deferred,
because heartbeat rounds are unreachable for T1 (the U18/D3
refutation), recorded in the module docstring.

- S3's chain consumes only O-C1 + `appliedWindow` + the local apply
  facts — no commit RULE at all. Election-safety (S1) consumes the
  commit axis NOWHERE: the U18 grep evidence (commitIndex absent
  from the S1 chain's content) re-verified at the statement level —
  none of the S1-fragment signature members (`NativeObligations`
  O1–O5) mentions commit.

**(1d) The route verdict — b′ empirical gate, MEASURED.** The census
(derivation: greps over `compat/verdi/VerdiCompat/` at this tip):

- The three chain files (ElectionSafety 1,766 + CandidateEntries
  1,199 + LeaderLogs 2,040 = 5,005 lines, 58 theorems) contain
  **ZERO direct handler unfolds**: the complete `unfold`/`simp`
  target census is `update` ×115 (net plumbing), `wonElection` ×3,
  `dedup` ×3, `eraseOne` ×2, `div2` ×2 + four pure-List simp lemmas
  — ALL dialect-neutral. Every concrete-handler consumption is
  quarantined in `ElectionSpecLemmas.lean` (1,406 lines, ~50 spec
  lemmas), which under b′ IS the Verdi-dialect obligation-discharge
  file.
- **The b′-resistant residue in the S1 chain: ZERO invariant-layer
  proofs.** The residue is exactly (i) the induction-principle
  plumbing (`RefinedProofStructure.lean`'s
  `refined_raft_net_invariant` hands obligations concrete handler
  equations — under b′ one new signature-parametric induction
  principle replaces it, same shape, ~1 file) and (ii) the
  per-dialect discharge layer (definitionally per-dialect).
- **The measured ADAPTS driver** (found by reading, the kind of
  fact the audit doctrine says only reading finds): etcd's
  `becomeLeader` → `reset(r.Term)` → `trk.ResetVotes()`
  (raft.go:952→800→813) — an etcd leader retains NO tally, so T3's
  `votes_received_leaders` (leader state carries
  `wonElection votesReceived`, ElectionSafety.lean:702) cannot port
  statement-intact. The signature states the quorum fact at the
  TRANSITION (`leaderEntry`, O4) and carries it in a victory GHOST
  (verdi-raft's `electoralVictories` device promoted to the family
  interface). Classification: `cronies_correct` → ADAPTS (reshaped
  to victory form); everything else in the S1 chain → PORTS;
  the discharge layers → per-dialect by definition.
- Per-lemma classification of the S1 chain (each vs its T3 source,
  recorded in `NativeObligations.lean` docstrings):
  `votes_le_currentTerm` PORTS (consumes O1+O3b);
  `votes_correct` PORTS (O1+O2+O3a/b; the six `votes_ok_*` step
  obligations become one obligation-parametric preservation lemma —
  plumbing, not reasoning); `candidates_vote_for_selves` PORTS with
  one added obligation member (candidate entry sets vote := self;
  etcd discharges in `becomeCandidate`, raft.go:928);
  `cronies_correct` ADAPTS (victory-ghost reshape, above);
  `pigeon`/`dedup`/`div2`/`wonElection_one_in_common` PORTS-VERBATIM
  (dialect-free math; discharges the quorum-intersection member);
  `one_leader_per_term_ghost` + exit PORTS (assembly, proved this
  unit — see slice 2).

**S2/S3 route sizing** (anchored: arc-3 unit 2 shipped the WHOLE
election-safety chain — ElectionSpecLemmas 730 lines-at-tip +
ElectionSafety 1,766 — in ONE unit, `campaign-arc3-log.md` unit-2
final entry; throughput ≈ 2.5k proof lines of this class per unit):

- **(a) projection redesign — DEAD for S2/S3, state it plainly**:
  there is nothing to transfer (no lattice SMS/log-matching proof
  exists), the commit axis has no lattice image (C1 theorems), and
  the noop erasure pays an index-remap tax on every statement. The
  route's only argument was reusing proved lattice content; the
  content does not exist.
- **(b′ family, full protocol superstructure)**: leader-completeness
  + SMS + log-matching proved once from the signature. Anchor:
  verdi-raft's remaining SMS block is larger than everything T3 has
  ported so far (T3's 9.9k lines ≈ arc-3 units 1–4);
  StateMachineSafetyProof.v is verdi-raft's heaviest file. Estimate
  **≈ 4–8 units**, family-level (amortizes over T2, dialect
  variants), schedulable POST-T1.
- **(b′ T1-scoped, the ghost-history chain) — THE LEADING ROUTE for
  T1's leaf**: under the twin driver the campaign event is issued
  once, pre-loop (twin-chdriver.go:44), and nothing else reaches
  `becomeCandidate` (no ticks ⇒ no hup) — so at most one election,
  winner node 1, and a SINGLE append-only history `H`. Chain
  H1(single-writer, driver-shaped) → H2(hist well-formed) →
  H3(logs-are-prefixes) → H4(applied-from-hist; the ONLY link that
  consumes the commit axis, via O-C1/2/3 + appliedWindow) → the S2/S3
  leaves — leaf assemblies PROVED this unit (`s2_agree_of_hist`,
  `s3_term_of_hist`: two applied records at one index both equal
  H's entry; term-mono transfers through histAt). Statement chain =
  12–16 lemmas at spec level, all obligation-consuming except H1
  (driver-shaped, survives T2's num_parties — the generalized driver
  keeps the single pre-loop campaign). Estimate **≈ 1.5–2 units**
  (chain ≈ unit-2-class statements but far fewer and smaller;
  calibration from slice 2's measured per-lemma costs), PLUS the
  checker-implication transfer through absTwinRead which is C-wave
  round-lemma work either way. LINEAGE: history/auxiliary-variable
  refinement (Abadi–Lamport); property transfer through the mapping.
- **(c) etcd-faithful full re-proof without the signature**: strictly
  dominated by (b′ full) — same NEW volume, no family reuse. Dead.

**RECOMMENDATION (decision input)**: T1's S2/S3 leaf via the
T1-scoped ghost-history chain over the signature's commit obligations
(1.5–2 units, sequence after C3's native S1); commission the family
SMS superstructure (4–8 units) only at T2/T5 planning, as family
investment — it is not on T1's critical path.

**The named fallback (one paragraph, per the re-target's cap):** a
patched Verdi-dialect twin subject got LESS attractive on this
unit's evidence: the b′ risk it hedges — "the signature refuses to
factor" — is now measured SMALL at the invariant layer (zero
residue; the A4 axis dissolves into one obligation envelope, proved
both halves), so the hedge would buy little while its recorded cost
stands (layer-B/C artifacts are subject-exact literal chains — the
equation ladder forks, only the generic kit carries). Nothing found
this unit makes the fallback more attractive.

### Slice 2 — THE NATIVE-S1 SIZING PROBE (charter 2, b′-framed)

Shipped in `NativeObligations.lean` (self-contained, machine-free —
imports nothing; elaborates in seconds; kernel-checked in the same
build as everything else):

- **The etcd-abstract vocabulary**: `ENode` (the C1 adapter probe's
  record + the poll record `votesRec` = `trk.Votes`) and the
  election-fragment specRound functions, each line-cited to the
  subject: `specBecomeCandidate` (raft.go:921-935 + reset 800-829),
  `specRecvVote` (the Step preamble 1120-1146 + the vote case
  1231-1284: `canVote` + `isUpToDate`, grant records the vote),
  `specRecvVoteResp` (poll 1094-1102 → quorum → becomeLeader
  952-990 with the tally-clearing reset and the noop append).
- **The obligation signature, S1 fragment** (`ElectObligations`):
  O1 termMono, O2 votePersist, O3a/b ghost-vote growth+faithfulness,
  O4 leaderEntry (victory-ghost quorum at the transition), O5a/b
  victory persistence + leader term stability — each member's
  docstring names BOTH discharges (Verdi spec-lemma cite + etcd
  code-path cite): the vacuity discipline held member-by-member.
- **The native statement**: `oneLeaderPerTerm` over `SNet`
  (T3's `Properties.lean:27` reshaped to the etcd-abstract axes).
- **The superstructure skeleton**: `Skel_votesLeCurrentTerm` /
  `Skel_votesCorrect` / `Skel_leaderVictory` /
  `Skel_oneLeaderPerTerm` as named Props (never unproven theorem
  stubs), classified PORTS/PORTS/ADAPTS/PORTS in-docstring.
- **THE THREE PROVED CALIBRATION LINKS** (all
  [propext, Quot.sound]-clean, `AxNative` probe readout verbatim in
  the artifacts):
  1. `majority_quorums_intersect` (+2 counting helpers): two
     majority quorums share a voter — the quorum-intersection member
     discharged for the majority dialect. ~40 lines vs T3's
     ~170-line dedup/pigeon ring — a measured b′ dividend (the
     quorum-SET form skips the tally-list dedup normalization; tally
     lists stay dialect-side). Cost: 3 elaboration iterations
     (one simp-loop fix, one Mathlib-absent `push_neg` rewrite).
  2. `oneLeaderPerTerm_of_chainInv`: the exit assembly — T3's
     `one_leader_per_term_ghost` 27-liner (ElectionSafety.lean:
     1722-1748) re-derived over the signature bundle in 12 lines,
     first try (the victory bundle pre-packages what T3 reassembles
     from cronies' four conjuncts).
  3. `specRecvVote_termMono` / `specRecvVote_votePersist`: the
     etcd discharge layer's per-lemma specimen — O1/O2 discharged
     against the spec function by case analysis, ~25 lines, one
     iteration.
  Measured per-lemma cost at this class: minutes to tens of minutes
  — consistent with the arc-3 unit-2 throughput anchor.
- **The commitIndex-avoidance claim, formally checked at statement
  level** (charter 2's verify-or-refute): the S1-fragment signature
  and superstructure statements contain NO commit field references —
  `committed` appears in `ENode` (vocabulary) but in none of O1–O5,
  `ChainInv`, or the skeleton Props (grep over the module). The C1
  grep evidence is VERIFIED at the statement level: election safety
  never consumes the mismatched axis.

**UNIT-COUNT ESTIMATE for the full native S1 (the C3 leaf), with the
calibration evidence** (each line derivation-anchored above):

- signature finalization + the obligation-parametric induction
  principle (the RefinedProofStructure analog): **~0.5–1 unit**;
- superstructure port of the votes/victory chain (PORTS with
  re-plumbed hypotheses; reasoning intact per the zero-residue
  census; the one ADAPTS reshape is cronies→victories): **~1 unit**
  (the original arc-3 port of the same chain from Coq was 1 unit;
  re-plumbing existing Lean is not harder);
- the etcd discharge layer (election fragment: ~12–18 lemmas at the
  link-3 specimen cost, incl. the ghost-attachment rules):
  **~0.5 unit**;
- the S1 checker-implication leaf statement (false-delta of
  twin-lib.go:272-278 from `oneLeaderPerTerm` through absTwinRead):
  **~0.5 unit** (shared with C3's induction-skeleton work).
- **TOTAL ≈ 2.5–3 units** for the family-grade native S1.
  The Verdi-side discharge (making T3's lattice literally an
  instance — the family claim's validation) is **+0.5–1 unit**,
  optional for T1.
- **The T1-scoped floor, priced for contrast**: under the driver,
  S1's disagreement branch is unreachable via `Skel_onlyNodeOneClaims`
  ("only node 1 ever leaves follower" — one invariant, no votes, no
  quorum math): **~0.5 unit**. Driver-shaped; buys nothing for the
  family; survives T2. The coordinator's re-sequencing call — the
  signature route is the 2–2.5-unit premium that buys the family
  interface.

### Slice 3 — THE HARVEST-GRANULARITY QUESTION (charter 3)

**The instrument**: `ChoiceSiteProbe.lean` (gitignored) — the U18
census walk re-run with a SITE-LABELED consumption event stream: at
every step where the choice stream shrinks, the pre-step config is
classified (`.mapIterK` ⇒ mapIter; `.stmtOpK (.appendSlice)` ⇒
appendSpill; anything else prints OTHER — fail noisy). Ground truth:
the sequential machine consumes at exactly two sites
(`ChoiceSite.policy`, GoLean/GoCore/State.lean:207-256 — the l*/sched
sites are the multi-goroutine machine's and never pop here).

**The walk replicated the pinned run to the step, independently
again**: 711,616 steps, final na = heap = 36,376, observable values
(viol 0, claims 1, committed 6, complete 1, floor 1) — the third
independent replication (Arc-2, U18, this probe). 345 consumptions
total = **245 mapIter + 100 appendSpill, 0 OTHER** (the classifier
covered every draw; `artifacts/choicesite-events.tsv`, 912 events).

**Attribution** (CONSUME rows joined to the nearest preceding watched
CALL; the full bucket table is reproducible from the TSV):

| bucket | mapIter | appendSpill |
|---|---|---|
| raft.NewRawNode (init) | 108 | 9 |
| newTwin (init) | 0 | 2 |
| becomeFollower (init 3× + in-run 2×; reset→Visit) | 38 | 24 |
| becomeCandidate / becomeLeader / poll / campaign spine | 26 | 2 |
| maybeCommit (arm; quorum CommittedIndex) | 27 | 0 |
| bcastAppend (arm/harvest; tracker Visit) | 18 | 0 |
| handleAppendEntries (arm; log append) | 0 | 18 |
| applyUnstableEntries (RING) | 1* | 18 |
| acceptReady (RING) | 0 | 13 |
| maybeSendAppend / appendEntry (arm+ring sends) | 0 | 13 |
| main.twin.say (driver glue = the round pick) | 27 | 1 |

(*) the single "in-ring" mapIter at step 100,827 is the FIRST driver
pick — it precedes the first `main.twin.say` so it buckets under the
campaign harvest's last watched call. Corrected: driver picks = 28 =
the 28 deliver rounds, exactly one value-relevant mapIter draw per
round, NONE inside the harvest ring.

**THE VERDICT — the harvest ring is choice-CONSUMING but
VALUE-DETERMINISTIC given the round's inputs**:

- Every in-ring mapIter draw (and every arm-side library draw —
  Visit, quorum CommittedIndex/TallyVotes, campaign's id collection)
  is immediately CANONICALIZED: `tracker.Visit` sorts
  (raftsubject/tracker/tracker.go:184-200), `MajorityConfig.Slice`/
  `CommittedIndex` sort (raftsubject/quorum/majority.go:109-155),
  `VoteResult` only counts (order-insensitive), campaign sorts its
  id slice (raft.go:1062-1070). The draw VALUES never reach the
  post-state.
- Every appendSpill draw affects capacity/layout only — exactly the
  latitude the landed equations' alloc-symbolic form + spill
  families already absorb.
- One honest caveat for the ∀-stream form: the NUMBER of appendSpill
  draws per round is stream-dependent (a generous earlier capacity
  pick avoids a later spill) — the same RE-SPILL residual family the
  handler equations already carry; the mapIter arity per round IS
  stream-independent (one draw per iteration regardless of pick).
- The U18 claim "storage-resp sub-rounds choice-free" is CONFIRMED
  and sharpened: no draws bucket under the nested storage-resp
  spans; the ring's draws sit in the Ready-assembly/send/append
  spans and are all appendSpill.

**The two shapes, priced** (step counts from the U18 phase
decomposition — HasReady ~800, Ready/readyWithoutAccept/
applyUnstable ~1,500, acceptReady ~2,900, Advance + nested
storage-resp Step ~2,000, second Ready round ~1,290; ring total
9–14k steps/round; mirror rate ~30-40 steps/s per U18):

- **BATCHED per-cycle lemma** (one equation per reachable round
  kind, whole-ring span): ~6-7 reachable kinds × 4-8 min mirror
  each ≈ **30-55 min kernel across the ladder**, 6-7 statements, no
  cross-kind reuse (every kind re-walks the shared shells). Value:
  no dependence on C2a's composition instrument WITHIN the ring.
- **PER-ARM (sub-ring) equations**: 5-6 payload-parametric
  statements (HasReady / Ready-assembly / acceptReady / Advance +
  storage-resp / second-Ready), each proved ONCE — the shells are
  the same code across round kinds with message-field-symbolic
  payloads — ≈ 8.5k steps walked once ≈ **4-5 min mirror total**,
  plus C2a-dependent composition lemmas. Cross-kind reuse ≈ 5-6×.

**RECOMMENDATION (decision input)**: per-arm sub-ring equations as
C2c's primary shape — the determinism verdict makes their
conclusions stream-independent (modulo spill widths), the shells'
cross-kind identity is what the ~6-10× kernel-volume saving rides
on, and C2a (already commissioned first in the ladder) is exactly
the instrument that composes them. The batched per-cycle form is the
recorded fallback if C2a misses its 3-unit hard stop: 30-55 min of
mirror kernel and 6-7 standalone statements, viable but
non-amortizing. Either way the ring needs NO new choice-handling
machinery — the alloc-symbolic/spill-family forms suffice
(this slice's load-bearing answer for C2c's design).

### [AGENT] calls this unit (tagged)

1. [AGENT] The b′ empirical gate answered by STATIC census (greps
   over the chain files' tactic surface) rather than by attempting a
   mechanical re-factor: the unfold census is the direct measurement
   of "factors through obligations vs unfolds handlers", at probe
   cost. The 3 proved links are the dynamic complement.
2. [AGENT] The signature drafted at PROBE SCALE in a shipped module
   (statements only + calibration proofs) rather than probe-only:
   the charter's file discipline allows new Specs/Raft/Native*
   modules, and the C3 unit will consume these statements directly —
   but nothing imports them yet, and no aggregator was touched (the
   hard no-edit rule; the wave-boundary landing wires them).
3. [AGENT] `specRecvVoteResp` models the twin's PreVote-off,
   checkQuorum-off config (the pinned Config, twin-lib.go:207-215) —
   config-latitude members (lease check, PreCandidate) are OUT of the
   S1 fragment deliberately, noted in the docstring; the family
   signature grows those members when a dialect needs them.
4. [AGENT] Hatch hygiene: the first gate run's escape-hatch preflight
   flagged a PROSE-ONLY token in a module docstring (the U17
   admit-token false-positive class — but in a proofs file the
   preflight scans, unlike U17's docs-side case), so the docstring
   was REWORDED rather than argued with (gates are speedbumps, not
   review targets); final hatch grep over both modules: 0 hits.
5. [AGENT] Memory discipline: the cold build and the census walk ran
   concurrently only after a `free -g` check (73G available, above
   the 40G floor); no third heavy job launched beside them.
6. [AGENT] The two new modules are DELIBERATELY UNIMPORTED: wiring
   them into the default build means editing the aggregator
   (`proofs/GoLeanProofs.lean`) — an existing tracked file the
   no-edit rule forbids this lane. Their verification is therefore
   the explicit capped target builds (green: `lake build
   GoLeanProofs.Specs.Raft.NativeObligations` / `...NativeS23Route`)
   plus the `AxNative` axiom readout, recorded in slice 2; the
   default-target `lake build` (528 jobs, green) covers the rest of
   the tree. The wave-boundary landing adds the two import lines —
   the landing coordinator's one-line edit, called out here so it is
   not forgotten.

### What-this-taught-us

- (a) The decisive S2/S3 fact was NOT on the mismatch axes at all:
  T3 simply has no SMS/log-matching proofs — routes were being
  compared on transfer costs of content that does not exist. A
  ten-minute statement-vs-proof census of the lattice would have
  settled the route frame before the A4 probe was designed.
- (b) The A4 kill-point is an artifact of comparing POINT rules; at
  obligation granularity both dialects inhabit one envelope
  (`followerCommitOk`, both halves proved in ~2 lines each). The
  two-bounds doctrine's protocol-level analog is real and cheap to
  state — the family route's core claim survived its first formal
  contact.
- (c) The obligation census metric (unfold-targets in invariant
  proofs) is a reusable instrument: any future "does layer X factor
  through interface Y" question has the same shape — measure the
  tactic surface, don't argue the architecture.
- (d) etcd's tally-clearing `becomeLeader` is the concrete reminder
  that state-carried invariants (Verdi's `votes_received_leaders`)
  must become transition-scoped + ghost-carried in the family frame;
  reading the subject found it, no test would have.
- (e) OPERATIONAL, for the lane ledger: a COLD full build of this
  tree at default lake parallelism OOMs a 48G cgroup in the heavy
  Raft-literal tail (two independent kills at jobs ~512/530 and
  ~471/528; `Result=oom-kill` on the scope, machine-wide memory
  ample) — and the kill is SILENT in the log (no "Build completed"
  line is the only tell; the U18-era green-line check is the right
  habit). Cold worktree bootstraps should build under
  `GOLEAN_MEM_MAX=64G` (green here: "Build completed successfully
  (528 jobs)"; this lake has no jobs flag to narrow parallelism);
  warm-state gates at 24G are unaffected (U18's gate record).

## SC1 exit (2026-08-26, tip = this commit)

**CHECKPOINT (recomputed):** worker commits since the branch base
3bbb0f10: this single commit (two tracked modules + this log; probes
and TSVs are gitignored artifacts). Deliverable state vs the SC1
charter, re-target applied:

1. THE S2/S3 ROUTE QUESTION — **DELIVERED**: checker census
   line-exact (slice 1a); needed invariants as Props (1b +
   `NativeS23Route.lean`); the commit-axis check VERIFIED at
   statement level against the signature, with the A4 dissolution
   PROVED both halves and the one heartbeat caveat named (1c); the
   b′ empirical gate MEASURED (zero handler-unfold residue in 5,005
   chain lines; the spec-lemma layer is the discharge file), routes
   sized with the T3 statement-only finding as the decisive fact,
   recommendation + skeleton chain shipped (1d).
2. THE NATIVE-S1 SIZING PROBE — **DELIVERED**: `oneLeaderPerTerm`
   stated natively over the specRound election fragment; the
   signature drafted member-by-member with dual discharge cites;
   the superstructure skeleton classified PORTS/ADAPTS/NEW; THREE
   chain links proved end-to-end (quorum intersection ~40 lines,
   exit assembly 12 lines, etcd O1/O2 discharges ~25 lines — all
   [propext, Quot.sound]-clean, `AxNative` readout); unit estimate
   2.5–3 units (family) vs 0.5 (driver-scoped floor), each line
   derivation-anchored.
3. THE HARVEST-GRANULARITY QUESTION — **DELIVERED**: the
   site-labeled census (345 draws = 245 mapIter + 100 appendSpill,
   0 unclassified; third independent replication of the pinned run);
   the ring is choice-consuming but value-deterministic (all
   library mapIter draws sort/count-canonicalized; appendSpill =
   capacity latitude the equation forms absorb); batched vs per-arm
   priced (30–55 min vs 4–5 min mirror kernel; 6-7 standalone vs 5-6
   reused statements); recommendation: per-arm as C2c primary,
   batched as the C2a-failure fallback.

Zero sorry / native_decide / new axioms in the two shipped modules
(hatch grep after the preflight-driven rewording: 0 hits); all eight
proved lemmas within [propext, Quot.sound]. Nothing merged; nothing
existing edited; the branch ends at this commit for the operator's
wave-boundary handling.

- 2026-08-26 SC1 gate record (same-commit convention): unit-end gate
  `GOLEAN_ALLOW_NO_DIFF=1 GOLEAN_MEM_MAX=24G scripts/ci` at the exit
  tree — **RESULT: FAIL, exit 1 — 21 ok steps, 7 notes (incl. the
  two sanctioned no-diff notes), and EXACTLY ONE red, structural and
  fully characterized** (`artifacts/ci-arc4b-sc1.log`, gitignored):

  ```
  FAIL proofs-file audit coverage (un-swept proof file — import it from Audit.lean or allowlist with a reason)
  ```

  naming precisely the two new modules ("not in the audited import
  closure nor on the standalone allowlist"). This is the ci F2
  tamper check doing its designed job on exactly this lane's
  situation: a new proofs/*.lean enters the audited build only via
  an import reachable from Audit.lean/GoLeanProofs.lean — and BOTH
  wiring points (the aggregator, the `STANDALONE_PROOFS` allowlist
  inside `scripts/ci`) are existing tracked files this lane's hard
  no-edit rule forbids touching. RULE CONFLICT, resolved fail-closed
  per the operating contract: the charter's file discipline (which
  exists so this branch lands conflict-free at the wave boundary)
  outranks a green gate line that only an out-of-scope edit could
  buy; the red is recorded verbatim instead of engineered around,
  and the compensating verification is on the record — both modules
  kernel-checked green as explicit capped build targets, the
  `AxNative` #print-axioms readout ([propext, Quot.sound] across all
  eight proved lemmas), hatch grep 0. **The landing action that
  turns this green is two import lines in `proofs/GoLeanProofs.lean`
  at the wave boundary** — the landing coordinator's edit, called
  out in [AGENT] call 6. Every other gate step ok; the
  comparator-landmark note now reads STALE at 148 commits
  (report-only) — stands escalated for the operator's merge step, as
  at U8–U18. First gate run additionally caught the docstring prose
  token (fixed, [AGENT] call 4); no other delta between runs.

# C3 — the native S1 chain over the obligation signature (worker 2)

Unit C3, branch `campaign-arc4b` @ base 740c719e (SC1's exit tip),
one writer, NEW FILES ONLY (unchanged hard rule). Charter: (1) the
signature + obligation-parametric induction, (2) the S1
superstructure port (re-plumbing per SC1's zero-residue census, the
ADAPTS victory-ghost reshape), (3) the etcd discharge layer complete
for S1, (4) the S1 checker leaf through the I4 interface premise.
Design of record: the campaign worktree's
`docs/2026-08-26_campaign-flexibility-redesign.md` (§3 I1/I4; §7
middle-path calibration BINDING — no speculative signature members).

## C3 entry — 2026-08-27

- Slice 0 — SUCCESSOR RE-VERIFICATION of SC1's top claims, all four
  re-run at launch, VERIFIED:
  1. tip 740c719e, `git status` clean — verified verbatim ("nothing
     to commit, working tree clean").
  2. Both Native modules green as explicit capped build targets
     (warm, `GOLEAN_MEM_MAX=48G scripts/capped lake build
     GoLeanProofs.Specs.Raft.NativeObligations
     GoLeanProofs.Specs.Raft.NativeS23Route` from `proofs/`):
     "Build completed successfully (3 jobs)". [Note for successors:
     the target names resolve only from `proofs/` — the root
     lakefile is the GoLean package and rejects them.]
  3. Fresh `AxNative` readout (capped `lake env lean`), all eight
     lemmas within [propext, Quot.sound] — precisely: 3 report
     [propext, Quot.sound] (majority_quorums_intersect,
     oneLeaderPerTerm_of_chainInv, specRecvVote_votePersist), 5
     report [propext] alone (a subset — SC1's "within" claim holds
     member-by-member).
  4. Hatch grep over both modules: zero `sorry`/`native_decide`/
     axiom declarations; the single textual hit is the prose
     substring "axiomatization" in NativeObligations.lean:52's
     LINEAGE docstring (the U17/SC1 prose-token class; SC1's gate
     preflight already accepted it).
  Launch state: 119G available (well above the 40G floor); builds
  this unit at GOLEAN_MEM_MAX=48G warm per SC1's ops note (e).
- [AGENT] read-first per charter: SC1's full log, both Native
  modules, the flexibility-redesign note (§3 I1/I4, §7 binding), the
  twin checker's S1 span re-read at source (twin-lib.go harvest:
  claims from Ready SoftState == StateLeader; `leaderOf : term ↦
  node`, violation on a DIFFERENT later claimant — note the check is
  CROSS-TIME, claims accumulate across harvests), T3's
  `votes_correct` block (ElectionSafety.lean:180-265) for the
  conjunct census before re-plumbing.

### Slice 1 — the signature + the obligation-parametric induction
(charter part 1)

Shipped in `proofs/GoLeanProofs/Specs/Raft/NativeS1Chain.lean` (316
lines, 15 theorems, imports NativeObligations only):

- `ReachRel` (RTC of an abstract dialect step) + `invariance` — THE
  obligation-parametric induction principle, the b′ replacement for
  T3's `refined_raft_net_invariant`: preservation premises consume
  signature members only, never handler equations (exactly the
  ~1-file reshape SC1's zero-residue census predicted). LINEAGE:
  standard RTC invariance / Abadi–Lamport ghost refinement.
- `Seed` (deliberately MINIMAL: empty ghost votes + no leaders —
  victory-emptiness is NOT needed, `leaderVictory` is vacuous
  through `noLeaders`) and `GoodReach step N₀ N := Seed N₀ ∧
  ReachRel step N₀ N` — the exact instantiation of SC1's abstract
  `Reach` ("closed under step, containing the seed").
- The signature was NOT extended: no new members, no
  prevote/learner axes (§7 binding, and the demand never
  materialized — see the cross-time note below). n-generic holds by
  construction: `voters : List Nat` is the only configuration
  parameter; no party-count literal appears in any theory module
  (the witness's `voters3 = [1,2,3]` is an instance).

### Slice 2 — the S1 superstructure port (charter part 2)

Same module; "re-plumbing, not re-reasoning" held to the letter:

- `FullInv` = votesLe (PORTS, T3 ElectionSafety.lean:36) + oneVote/
  coherent (PORTS, T3:465 — T3's SIX `votes_ok_*` step lemmas
  became ONE obligation-parametric preservation lemma
  `FullInv.step`) + nonzero (plumbing auxiliary: the Nat-encoded
  vocabulary carries what T3 gets from `Option name`'s `some`) +
  leaderVictory (the ADAPTS reshape: victory-ghost form, consumes
  O4+O5a/b+O3a). A recorded b′ SIMPLIFICATION: T3's third
  `votes_correct` conjunct (the converse,
  `currentTerm_votedFor_votes_correct`, T3:201) is NOT carried —
  its only consumer was T3's votes_nw/cronies plumbing, which the
  victory ghost absorbs.
- **The native `one_leader_per_term`** (quoted verbatim in the exit
  block below): dialect-parametric, proved from `ElectObligations`
  alone via `fullInv_reachable` + SC1's link-2 assembly.
- **`native_one_leader_per_term_cross_time`** — NOT in the plan,
  demanded by the checker re-read (slice 0): the twin's S1 check is
  CROSS-TIME (`leaderOf` accumulates claims across harvests), and
  per-net election safety does not imply it. No new signature
  member was needed: O3a starred (`ghostVotes_mono_star`) carries
  the earlier observation's quorum votes to the later net, where
  `oneVote` closes — the victory-ghost device paying for exactly
  what SC1 promoted it for.
- All four SC1 skeleton Props discharged at the `GoodReach`
  instantiation (`skel_*_proved`), obligation-parametrically — for
  every discharging dialect at once.

### Slice 3 — the etcd discharge layer, complete (charter part 3)

`proofs/GoLeanProofs/Specs/Raft/NativeEtcdDischarge.lean` (671
lines, 23 theorems):

- `EStep voters` — the etcd election-fragment step over `SNet`:
  one specRound function per constructor, frame by function update,
  ghost rules exactly per the signature docstrings. Constructor
  premises, each recorded in the module header: `hgen` (response
  genuineness = T3's `votes_nw` absorbed as a receive premise, per
  the SNet docstring's stated design), `htally : TallyOK` (nodup
  keys ⊆ voters + ghost-faithful grants), `hfrom ∈ voters`,
  `hc/hi ≠ 0` (etcd ids nonzero, 0 = None sentinel).
- **`etcd_discharges : ElectObligations voters (EStep voters)`** —
  every S1 member discharged (O1/O2 riding SC1's link-3 specimens;
  O4 from the winning branch's quorum guard + TallyOK + genuineness;
  O3b from the grant/campaign ghost shapes; O5b from the branch
  lemmas' term stability).
- **The `TallyOK` premise is proved REDUNDANT on the reachable set**
  (`tallyOK_step`/`tallyOK_reachable`): it is an inductive invariant
  of `EStep` from empty-tally starts, so the guard prunes no
  reachable behavior — the honesty capstone for stating it as a
  premise (obligation members quantify over ALL nets, where a tally
  is garbage).
- Headline: `etcd_one_leader_per_term` (native chain × etcd
  discharge).

### Slice 4 — the S1 checker leaf (charter part 4, I4-scoped)

`proofs/GoLeanProofs/Specs/Raft/NativeS1CheckerLeaf.lean` (162
lines, 4 theorems):

- `ClaimTrace` — the observation-trace abstraction of the harvest
  loop (claims in order, each on a net reachable from the previous
  observation point; truncation allowed anywhere); `S1Delta` — one
  term claimed by two distinct nodes (the `leaderOf` branch's
  condition, order-abstracted).
- **`S1CheckerInterface`** — the I4 interface premise, stated and
  scoped EXACTLY to S1 (§7: no general checker theory): claims come
  from the trace; violation implies delta (soundness direction
  only — the leaf needs nothing more; completeness is not
  demanded of I2). Its proof against the checker's real span
  through absTwinRead is the arc-4 lane's I2 work, per charter.
- **`s1_leaf`**: signature invariants ⇒ ¬violation, dialect-
  parametric; `etcd_s1_leaf` = the etcd instance. The spine is
  `claimTrace_agree` (pairwise agreement by trace induction:
  head/head refl, head/tail = the cross-time theorem, tail/tail =
  IH with the base advanced).

### Slice 5 — the non-vacuity witness (doctrine, not in the sized
plan; the discipline that caught a real bug)

`proofs/GoLeanProofs/Specs/Raft/NativeS1Witness.lean` (127 lines,
11 theorems): a concrete 4-step election on `voters3 = [1,2,3]`
(campaign → self-response → grant from node 2 → victory at 2-of-3,
noop appended, tally cleared — the ADAPTS driver live in the data),
discharging EVERY chain premise by computation: `witness_leader`
(the final net really has a leader — the headline is not vacuous
over it), `witness_oneLeaderPerTerm`, `witness_s1_leaf` (end-to-end
through a concrete ClaimTrace + interface instance with the delta
Prop as the minimal violation instantiation), `witness_tallyOK`
(the redundancy corollary computed on the run).

**The bug the witness caught (fixed before commit, recorded):** the
first `EStep.campaign` pushed NO self ghost-vote, so a genuine
self-directed MsgVoteResp (etcd's `msgsAfterAppend` self-response,
raft.go:1066-1075) could never satisfy `hgen` — the subject's
actual 3-node election shape (self-vote + one grant = 2 of 3) was
UNSIMULABLE, i.e. the abstract dialect under-approximated the
subject and the safety theorem would not have covered real twin
traces. Fix: `campaign` pushes `(term+1, i)` for the candidate
itself — exactly where verdi-raft's `electionsData` records the
own-vote. The simulation direction (abstract ⊇ subject) is the
fidelity obligation here; the witness construction is what made
the gap visible.

### The optional Verdi-instance validation: NOT attempted, with the
reason on record

SC1 priced it +0.5–1 unit (mapping T3's RefinedNet step into `SNet`
+ re-deriving the members from ~50 spec lemmas). Attempting it in
this unit's tail would have been a rushed half-instance. The
vacuity discipline's second-dialect evidence stands as: SC1's dual
discharge CITES per member, the proved two-dialect O-C3 envelope
demonstrators, and this unit's complete etcd instance. The full
Verdi discharge (making T3's lattice literally an instance) is
family-validation work — natural at T2 planning or as a small
dedicated slice.

### [AGENT] calls this unit (tagged)

1. [AGENT] The cross-time theorem added WITHOUT a signature
   extension: the checker re-read showed per-net S1 is not what the
   check tests; the first design sketch reached for a
   `victoriesNew` member (victory-record soundness) before the
   vote-monotonicity route made it unnecessary. §7's
   no-speculative-members rule decided it: the weaker signature
   carries the leaf, so the member was not added.
2. [AGENT] The `TallyOK`/`hgen` premises absorbed as step-relation
   guards rather than proved as a separate dialect-side invariant
   layer: obligation members quantify over all nets, so SOME
   reachability-scoped fact must enter somewhere; the guard form
   keeps `etcd_discharges` unconditional, and the redundancy proof
   (`tallyOK_reachable`) discharges the honesty debt the guard
   creates. `hgen` remains a genuine modeling premise (the votes_nw
   absorption the SNet docstring already commits to) — it is the
   recorded seam where the packet-level correspondence will attach
   when the fragment grows packets.
3. [AGENT] The self-vote ghost fix (slice 5) applied to `EStep`
   mid-unit rather than logged as a gap: the four modules are this
   unit's own new files (no landed consumer existed), the fix is
   two lines + two proof cases, and shipping a knowingly
   under-approximating dialect against the fidelity doctrine to
   preserve a slice boundary would have been process over
   substance.
4. [AGENT] `Classical.choice` eliminated rather than tolerated: the
   first axiom readout showed it entering through one `simp [hpv]`
   (the Nat `==` self-test) in `recordVote_keys_nodup`; replaced
   with `beq_self_eq_true'` (axiom-free), restoring SC1's
   [propext, Quot.sound] envelope across all 20 C3 theorems. Not
   required by any gate — done for parity with the lane's recorded
   readout discipline and the statement-TCB story's cleanliness.
5. [AGENT] Hatch hygiene, SC1's precedent applied preemptively: the
   prose token "admit no S1 delta" in the leaf's docstring (the
   U17/SC1 admit-token class) reworded to "carry no S1 delta"
   BEFORE the gate run; the remaining prose substring "axiom-clean"
   (NativeS1Witness.lean:6) is the same class as SC1's accepted
   "axiomatization" and passed the preflight (ok line in the gate
   record).
6. [AGENT] The new modules stay DELIBERATELY UNIMPORTED (SC1's
   [AGENT] call 6 extended): wiring them needs the aggregator or
   the `STANDALONE_PROOFS` allowlist — both existing tracked files
   the lane's hard no-edit rule forbids. The wave-boundary landing
   action is now SIX import lines (SC1's two + C3's four:
   NativeS1Chain, NativeEtcdDischarge, NativeS1CheckerLeaf,
   NativeS1Witness) in `proofs/GoLeanProofs.lean` — the landing
   coordinator's edit.
7. [AGENT] Memory discipline: 119G available at launch and at the
   gate run (sibling idle at both checks); all builds
   `GOLEAN_MEM_MAX=48G scripts/capped` warm (largest observed
   incremental build: 6 jobs, seconds), gate at 24G per the warm
   convention. No cold build was needed this unit (SC1's .lake
   state was warm).

### What-this-taught-us

- (a) THE WITNESS IS A FIDELITY INSTRUMENT, not ceremony: the only
  substantive bug this unit (the missing self-vote ghost, which
  silently under-approximated the subject and would have voided
  the safety theorem's coverage of real twin traces) was caught by
  CONSTRUCTING the concrete run, after all obligation discharges
  were already green. Axiom-clean, kernel-checked, and wrong-side —
  exactly the class the non-vacuity doctrine names. Corollary for
  the lane: dialect step relations get their witness IN THE SAME
  UNIT, always.
- (b) The re-plumbing estimate held because the reasoning really
  was dialect-free: `FullInv.step` re-derives T3's votes chain in
  one lemma with ZERO handler mentions — the b′ census metric
  (unfold-target counting) predicted the port cost correctly.
  The one thing the census could NOT see was the checker's
  cross-time shape — a STATEMENT-side fact found only by reading
  the checker again with the leaf in hand.
- (c) Guard-shaped absorption of network invariants (TallyOK/hgen)
  plus a redundancy proof is a reusable pattern for fragment
  dialects: unconditional obligations + reachability-scoped guards
  + "the guard is invariant-implied" keeps the interface clean
  without smuggling reachability into the signature. It is also
  exactly where the S2-wave's match-evidence member will attach
  (SC1's leaderCommitOk `certified` note).
- (d) Toolchain notes for successors, measured this unit: `cases`
  alternatives must NOT name the inductive's INDEX arguments (the
  relation's `N` — "too many variable names" otherwise); `split`
  cannot see through zeta-binders (`simp only [defName] at h` first,
  then `split at h`); `subst h` with `h : a = b` eliminates the
  RHS variable (reference the LHS afterwards); a bare Nat `==` in
  this tree resolves to `instBEqOfDecidableEq`, so
  `beq_self_eq_true'` is the axiom-free self-test lemma, and
  `simp` on the same goal pulls Classical.choice.

## C3 exit (2026-08-27, tip = this commit)

**CHECKPOINT (recomputed):** worker commits since SC1's tip
740c719e: this single commit (four tracked modules + this log's C3
section; probes `AxNativeC3.lean`/`AxBisect.lean`/`AxTry*.lean` are
gitignored artifacts). Deliverable state vs the C3 charter:

1. Signature + obligation-parametric induction — **DELIVERED**
   (`NativeS1Chain.lean`: `invariance`, `Seed`/`GoodReach`,
   n-generic by construction, signature NOT extended).
2. The S1 superstructure port — **DELIVERED** (same module:
   `FullInv` + `FullInv.step` + `fullInv_reachable` +
   `native_one_leader_per_term` + the cross-time form + all four
   SC1 skeletons discharged at `GoodReach`).
3. The etcd discharge layer — **DELIVERED**
   (`NativeEtcdDischarge.lean`: `EStep`, `etcd_discharges` over all
   seven members, `etcd_one_leader_per_term`,
   `tallyOK_step`/`tallyOK_reachable` redundancy capstone).
4. The S1 checker leaf — **DELIVERED** (`NativeS1CheckerLeaf.lean`:
   `ClaimTrace`/`S1Delta`/`S1CheckerInterface` (I4-scoped),
   `s1_leaf`/`etcd_s1_leaf`).
   PLUS the non-vacuity witness module (`NativeS1Witness.lean`),
   doctrine-mandated, which caught and fixed the self-vote-ghost
   under-approximation. The optional Verdi instance: not attempted,
   reason recorded above.

Volume (derivation: `wc -l` / `grep -c ^theorem` at this tip):
1,276 new lines, 53 theorems across the four modules (316/15 +
671/23 + 162/4 + 127/11). Zero sorry / native_decide / new axioms;
hatch grep over all four: prose-substring hits only
("axiom-clean", the SC1-accepted class); preflight ok in the gate
record.

**Cost vs SC1's 2.5–3-unit estimate:** the mandatory parts landed
in ONE worker session ≈ one unit of wall-clock at high proof
velocity — materially UNDER the family estimate. Where the
estimate was fat, derivation-anchored: (i) the superstructure port
priced T3's six-step-kind plumbing at ~1 unit, but the
obligation-parametric form needed ONE preservation lemma (the b′
dividend compounding — SC1's links already showed 40-vs-170-line
ratios); (ii) the discharge layer priced ~12–18 lemmas at
specimen cost, and the actual layer is 23 theorems but most are
two-line branch/frame facts; the only genuinely new content was
the TallyOK/hgen design (measured in decisions, not lines). What
the estimate did NOT contain and this unit paid anyway: the
cross-time re-statement and the witness-driven fidelity fix —
both absorbed. Sizing lesson for the lane: b′-frame ports of
census-verified-zero-residue chains run ~2–3x under the
port-anchored estimates; the un-estimable residue is
statement-side fidelity (checker shape, simulation direction),
which is where the actual risk lived.

**The native `one_leader_per_term`, quoted verbatim
(`NativeS1Chain.lean`):**

```lean
theorem native_one_leader_per_term {voters : List Nat}
    {step : SNet → SNet → Prop} (ob : ElectObligations voters step)
    {N₀ N : SNet} (hseed : Seed N₀) (hreach : ReachRel step N₀ N) :
    oneLeaderPerTerm N
```

with `oneLeaderPerTerm N = ∀ i j, (N.node i).state = 2 →
(N.node j).state = 2 → (N.node i).term = (N.node j).term → i = j`
(SC1's statement, unchanged), and the etcd instance
`etcd_one_leader_per_term voters : (empty-ghost, no-leader start) →
ReachRel (EStep voters) N₀ N → oneLeaderPerTerm N`.

- 2026-08-27 C3 gate record (same-commit convention): unit-end gate
  `GOLEAN_ALLOW_NO_DIFF=1 GOLEAN_MEM_MAX=24G scripts/ci` at the
  exit tree — **RESULT: FAIL, exit 1 — 21 ok steps, 7 notes (incl.
  the two sanctioned no-diff notes), and EXACTLY the ONE known
  structural red** (`artifacts/ci-arc4b-c3.log`, gitignored):

  ```
  FAIL proofs-file audit coverage (un-swept proof file — import it from Audit.lean or allowlist with a reason)
  ```

  now naming precisely the SIX lane modules (SC1's two + C3's
  four), each "not in the audited import closure nor on the
  standalone allowlist" — the same rule conflict SC1 recorded,
  resolved the same fail-closed way: both wiring points are
  existing tracked files the lane's hard no-edit rule forbids; the
  red is recorded verbatim, the landing action (six import lines in
  `proofs/GoLeanProofs.lean`) is the coordinator's wave-boundary
  edit. Every other step ok; the comparator landmark note reads
  STALE at 148 commits (report-only) — stands escalated for the
  operator's merge step, as at U8–SC1. No other delta.
- 2026-08-27 C3 compensating kernel checks (verbatim):
  - explicit capped build of all four new modules + SC1's two
    (warm, 48G): `Build completed successfully (6 jobs.)` — final
    line `✔ [6/6] Built GoLeanProofs.Specs.Raft.NativeS1Witness`.
  - fresh `AxNativeC3` readout over all 20 named C3 theorems
    (chain 9, discharge 4, leaf 4, witnesses 3): every line
    `[propext, Quot.sound]` or a subset (`invariance` axiom-free;
    `claim_reachable` propext-only) — after the [AGENT]-call-4
    Classical.choice elimination; the SC1 eight re-verified
    unchanged at slice 0.
  - hatch grep over the four modules: 0 code hits (prose
    substrings only, recorded above).

**PROPOSED NEXT CHARTER for this lane** (the expected one, now
re-anchored): **the T1-scoped S2/S3 ghost-history leaf** over the
signature's commit obligations — SC1's route (b′ T1-scoped): chain
H1 (single-writer, driver-shaped) → H2 (hist well-formed) → H3
(logs-are-prefixes) → H4 (applied-from-hist; the ONLY
commit-axis-consuming link, via O-C1/2/3 + appliedWindow) → the
proved S2/S3 leaf assemblies (`s2_agree_of_hist`,
`s3_term_of_hist`, already on the branch). SC1's estimate 1.5–2
units; this unit's measured b′ discount suggests the low end.
Available assets: the induction principle and `GoodReach` transfer
as-is; `EStep` extension with the append/commit fragment
(handleAppendEntries/commit arms + their ghost history) is the
natural first slice, WITH its witness run in the same slice (lesson
(a)). The I4 pattern replays for the S2/S3 checker interfaces
(apply-order abstraction in place of ClaimTrace).

# C4 — the T1-scoped S2/S3 ghost-history leaf (worker 2, continued)

Unit C4, branch `campaign-arc4b` @ C3's tip 33a0b423, same worker,
same hard rules (Native* new files + this log only). Charter (from
the coordinator's acceptance message, recorded): H1→H4 over
O-C1/2/3 + appliedWindow, building on `s2_agree_of_hist` /
`s3_term_of_hist`; binding disciplines (1) witness-in-same-slice
(now a lane convention), (2) §7 T1-scoped — the leaf consumes
exactly SC1's three commit-axis members; the heartbeat
match-soundness member STAYS OUT per D3 unless a witness run
demonstrates need (finding-to-log-first if so), (3) same gate
expectation. Landing manifest owed at exit.

## C4 entry — 2026-08-27

- Slice 0 — design read-back before code: SC1's §5 chain
  (NativeS23Route.lean), the commit-obligation Props (O-C1/2/3 +
  appliedWindow — consumed BY NAME as step premises below), the C3
  assets that transfer as-is (ReachRel/invariance, the I4 interface
  pattern, the witness discipline). Two statement-side findings, on
  the record before building:
  1. **SC1's S23 skeleton Props are typed over `SNet`, which cannot
     carry the apply data** (`ENode` has no applied record;
     `appliedOf : SNet → Nat → ...` has nothing to project from).
     The C4 chain therefore lives on an extended carrier `HNet`
     with the SAME logical shape per link; the SNet-typed sketches
     stand superseded (statement-only, zero consumers — no code
     change to SC1's file, per the no-edit rule).
  2. **`Skel_singleWriterHistory` as literally stated is falsifiable
     at its intended instantiation**: it quantifies TWO
     independently-reachable nets and claims prefix-comparability,
     but two traces diverging on different proposals produce
     incomparable histories. The chain needs (and C4 proves) the
     along-one-trace form (`hist_prefix_star`: N' reachable FROM N
     ⇒ hist N' extends hist N). Recorded as a statement bug in the
     SC1 sketch, found by attempting the instantiation — the
     third statement-side catch of this lane (checker cross-time,
     self-vote ghost, this).

### Slice 1 — the fragment + chain (charter items H1-H4)

`proofs/GoLeanProofs/Specs/Raft/NativeS23Chain.lean` (594 lines, 17
theorems):

- `Star`/`star_invariance` — the C3 induction principle in its
  polymorphic form (the SNet-typed `ReachRel` could not be reused:
  C3's modules are now existing tracked files under the no-edit
  rule; the general form subsumes both — a landing-time unification
  candidate, in the manifest below).
- `HNode`/`HNet` — the extended carrier (log as a Hist prefix,
  oldest-first; commit/apply cursors; the applied record). The
  ENode↔HNode log-convention projection is I2's absTwinRead
  concern, documented.
- **`HStep ldr tm certified`** — the T1 post-election fragment:
  `propose` (the ONLY history writer — H1's shape, structural),
  `leaderCommit` (premises: `commitInWindow` + `leaderCommitOk`,
  VERBATIM), `deliverAppend` (premises: payload-is-a-history-slice
  + `followerCommitOk` VERBATIM; duplicate-tolerant via
  `take (max len k)`), `applyStep` (premise: `appliedWindow`
  VERBATIM; the `nextCommittedEnts` slice shape). The obligation
  consumption is SYNTACTIC — the charter's "H4 via O-C1/2/3 +
  appliedWindow" is visible in the constructor types. `certified`
  is consumed by name and never inspected (the O-C2 seam for the
  S2-wave's match-evidence member, per SC1's note).
- **`HistInv`** — H2 (histIdx/histTermMono + the fixed-term
  auxiliary), H3 (`logsPrefix`, take-form; `leaderLog`: the
  leader's log IS the history), the O-C1/appliedWindow windows
  carried, and H4 in its strongest T1 form: `appliedTake` — the
  applied record IS `hist.take applied`. `HistInv.step` +
  `histInv_reachable` prove the whole bundle preserved (the list
  core is `take_append_window`: prefix + next log window = longer
  prefix).
- **H1 starred**: `hist_prefix_star` (the along-one-trace form —
  the slice-0 finding about SC1's two-net statement stands) and
  `appliedLog_prefix_star` (applied records are cumulative — the
  I2-side justification for the final-net interface shape below).

### Slice 2 — the leaves + the I4 interface (charter's leaf)

Same module:

- `mem_hist_histAt` — membership pins the `histAt` lookup (the
  bridge into SC1's proved assemblies).
- **`s2_of_histInv`** — two applied records at one index agree,
  across ANY two nodes, THROUGH `s2_agree_of_hist` (SC1's proved
  leaf, consumed as promised).
- **`s3_of_histInv`** — a node's applied sequence is strictly
  index-increasing and term-monotone positionally (H4 take-form +
  H2; the term half is `histTermMono` — `s3_term_of_hist`'s
  content at the positional level).
- **`S23CheckerInterface`** — I4, S2/S3-scoped, FINAL-NET form: a
  deliberate simplification vs C3's `ClaimTrace`, justified and
  recorded: S1's claims are observations of TRANSIENT state
  (leaders vanish — the trace matters), while applied records are
  CUMULATIVE (`appliedLog_prefix_star`), so the final net carries
  every apply the checker saw; the interface premise ties the
  violation branches to final-net deltas. The anomaly sub-check
  (EntryNormal typing) is the recorded I2-side scope note — not
  representable in the abstract vocabulary; every abstract entry is
  a proposal or the noop by construction.
- **`s23_leaf`** — chain invariants at the start ⇒ both checks'
  false-delta on every reachable final net (quoted verbatim in the
  exit block).

### Slice 3 — the witness (same-slice convention, binding)

`proofs/GoLeanProofs/Specs/Raft/NativeS23Witness.lean` (159 lines,
12 theorems): a six-step T1-shaped run at `ldr = 1, tm = 2` (the S1
chain's output instantiated), `certified := fun _ => True` (the
O-C2 seam's SHAPE exercised, content deferred to the S2 wave):
noop propose → command propose → leaderCommit 3 → follower 2
accepts the slice with commit advance → both nodes apply. Every
constructor premise discharged by computation on the closed data;
`wApplied` shows both nodes really applied the full 3-entry history
(non-vacuity over the final net); `wFinalInv` computes the
preservation induction on the run; **`wNoViol`** drives `s23_leaf`
end-to-end at the minimal (delta-Prop) interface instance. The
heartbeat member was NOT needed by any witness run (no tick is ever
driven — D3 stands; nothing to report to the log beyond this line).

### [AGENT] calls this unit (tagged)

1. [AGENT] The obligation members consumed as VERBATIM constructor
   premises rather than re-derived facts: makes the charter's
   commit-axis scoping mechanically checkable (grep the constructor
   types) and keeps the chain honest to SC1's envelope statements —
   the same guard-shape pattern as C3's TallyOK, without needing a
   redundancy proof (the premises here are the RULE, not a
   reachability fact).
2. [AGENT] `appliedTake` stated in its STRONGEST T1 form (the
   applied record equals the history prefix) rather than the weaker
   membership form: §7's two-axis test — the strong form is CHEAPER
   (one equation, one list lemma) and makes both leaves one-step
   corollaries; T1-scoped means taking the T1 structure's gifts.
3. [AGENT] The final-net interface shape (vs C3's trace-carrying
   `ClaimTrace`): chosen on the cumulative-vs-transient distinction
   and recorded with its justification lemma
   (`appliedLog_prefix_star`); the checker-side proof obligation it
   leaves to I2 is correspondingly simpler (no trace bookkeeping).
4. [AGENT] `Classical.choice` ACCEPTED this unit (C3 eliminated it
   for parity): the bisect (probe `AxTryC4.lean`) shows it enters
   through core stdlib lemmas `List.drop_take` and `List.take_add`
   themselves, not through our proof choices — re-proving stdlib
   internals to purge a standard axiom is representation-level
   grinding with zero consumers. Derivation on record; the envelope
   is the standard trio, as everywhere else in the tree.
5. [AGENT] Polymorphic `Star` defined fresh instead of reusing
   C3's SNet-typed `ReachRel` (no-edit rule on my own C3 files);
   the unification (ReachRel := Star on SNet) is a one-line-per-use
   landing-time cleanup, listed in the manifest — NOT done here to
   keep the lane conflict-free.
6. [AGENT] Memory discipline: 119G at C4 launch, 107G before the
   gate (sibling active but light); all builds 48G-capped warm,
   gate at 24G. The witness's `decide`s are all on closed ≤/min/max
   Nat facts over 3-entry lists — evaluated shapes, no
   unevaluated-proposition kernel risk (the #eval-first rule's
   class does not arise).

### What-this-taught-us

- (a) The witness discipline paid AGAIN, differently: no bug this
  time, but constructing the run forced the `deliverAppend` rule
  through the duplicate-delivery question (k ≤ len) and settled it
  fidelity-first (`take (max len k)`, etcd's stale-append
  tolerance) BEFORE the invariant proof calcified the wrong rule.
  The witness is design pressure, not just a bug net.
- (b) Statement-side risk again outran proof-side risk, as C3
  predicted: the unit's real decisions were the carrier correction
  (SNet cannot hold apply data), the H1 statement fix (two-net
  comparability is false), and the final-net interface shape — all
  found by attempting statements, none by proving. The proofs
  themselves ran at the measured b′ discount.
- (c) The strongest-invariant instinct (appliedTake as an equation)
  is the T1-scoping dividend in miniature: scoped structure makes
  strong invariants CHEAP, and strong invariants make leaves
  trivial. The family SMS superstructure will not have this gift —
  its 4-8-unit estimate should not be discounted by this unit's
  velocity.

## C4 exit (2026-08-27, tip = this commit)

**CHECKPOINT (recomputed):** worker commits since C3's 33a0b423:
this single commit (two tracked modules + this log's C4 section;
probes `AxNativeC4.lean`/`AxTryC4.lean` gitignored). Deliverables
vs the C4 charter: H1 (`hist_prefix_star`, corrected form) — H2/H3/
H4 (`HistInv` + `histInv_reachable`) — the commit axis entering
EXACTLY through the three SC1 members + appliedWindow as verbatim
constructor premises — the S2/S3 leaves through SC1's proved
assemblies — the I4-scoped checker interface + `s23_leaf` — the
same-slice witness (`wNoViol` end-to-end). Volume: 753 new lines,
29 theorems (594/17 + 159/12). Zero sorry / native_decide / new
axiom declarations; hatch grep over both modules: ZERO hits (prose
included).

**Cost vs SC1's 1.5-2-unit sizing:** the unit landed in well under
one worker session-equivalent — below even the low end, for the
reasons lesson (c) names: the T1 structure admits equation-strength
invariants, and the statement work (where C3 showed the cost
lives) had already been paid down by SC1's checker census and this
unit's slice-0 findings. The residual un-discounted work is real
but OUT of this unit by charter: the I2 checker-side proofs and
the S1↔S23 assembly composition (T1 wave), and the family SMS
superstructure (post-T1, do NOT discount its 4-8 units by this
velocity — lesson (c)).

**The S2/S3 leaf statements, quoted verbatim
(`NativeS23Chain.lean`):**

```lean
theorem s2_of_histInv {ldr tm : Nat} {N : HNet}
    (hI : HistInv ldr tm N) {i j : Nat} {e e' : Nat × Nat × Nat}
    (he : e ∈ (N.node i).appliedLog) (he' : e' ∈ (N.node j).appliedLog)
    (hidx : e.1 = e'.1) : e = e'

theorem s3_of_histInv {ldr tm : Nat} {N : HNet}
    (hI : HistInv ldr tm N) {i : Nat} {p q : Nat}
    {ep eq : Nat × Nat × Nat} (hpq : p < q)
    (hp : (N.node i).appliedLog[p]? = some ep)
    (hq : (N.node i).appliedLog[q]? = some eq) :
    ep.1 < eq.1 ∧ ep.2.1 ≤ eq.2.1

theorem s23_leaf {ldr tm : Nat} {certified : Nat → Prop}
    {N₀ Nf : HNet} (h0 : HistInv ldr tm N₀)
    (hr : Star (HStep ldr tm certified) N₀ Nf)
    {violS2 violS3 : Prop}
    (hIface : S23CheckerInterface Nf violS2 violS3) :
    ¬ violS2 ∧ ¬ violS3
```

- 2026-08-27 C4 gate record (same-commit convention):
  `GOLEAN_ALLOW_NO_DIFF=1 GOLEAN_MEM_MAX=24G scripts/ci` at the
  exit tree — **RESULT: FAIL, exit 1 — 21 ok steps, 7 notes (incl.
  the two sanctioned no-diff notes), EXACTLY the ONE known
  structural red** (`artifacts/ci-arc4b-c4.log`, gitignored):

  ```
  FAIL proofs-file audit coverage (un-swept proof file — import it from Audit.lean or allowlist with a reason)
  ```

  now naming precisely the EIGHT lane modules (SC1's two + C3's
  four + C4's two). Same fail-closed resolution as SC1/C3; the
  landing action is the manifest below. Comparator landmark note:
  STALE at 149 commits (report-only) — stands escalated for the
  operator's merge step, as since U8. No other delta.
- 2026-08-27 C4 compensating kernel checks (verbatim):
  - explicit capped build (warm, 48G): `Build completed
    successfully (5 jobs.)` — final line `✔ [5/5] Built
    GoLeanProofs.Specs.Raft.NativeS23Witness`.
  - fresh `AxNativeC4` readout over 15 named C4 theorems: every
    line within [propext, Classical.choice, Quot.sound]
    (`star_invariance`/`wRun`/`wApplied` axiom-free;
    `hist_prefix_star`/`appliedLog_prefix_star`/`wSeedInv`
    propext-only; the choice-bearing lines inherit it from stdlib
    `List.drop_take`/`List.take_add` — [AGENT] call 4's bisect).
  - hatch grep both modules: 0 hits.

## THE LANE'S LANDING MANIFEST (for the operator at the wave
boundary — what the merge needs beyond `git merge --ff-only`)

1. **The one edit that turns the known red green:** add the EIGHT
   import lines to `proofs/GoLeanProofs.lean` (or allowlist with
   reason in `scripts/ci`'s `STANDALONE_PROOFS` — importing is the
   right call; these are ordinary proof modules):
   `GoLeanProofs.Specs.Raft.NativeObligations`, `.NativeS23Route`
   (SC1), `.NativeS1Chain`, `.NativeEtcdDischarge`,
   `.NativeS1CheckerLeaf`, `.NativeS1Witness` (C3),
   `.NativeS23Chain`, `.NativeS23Witness` (C4). Then re-run
   `scripts/ci` — expect fully green (all eight kernel-check green
   standalone at this tip; the Audit sweep will then cover them).
2. **Optional same-landing cleanups (small, listed not demanded):**
   (a) unify C3's `ReachRel`/`invariance` onto C4's polymorphic
   `Star`/`star_invariance` (one-line-per-use); (b) SC1's
   `Skel_singleWriterHistory` and the SNet-typed S23 skeleton Props
   in `NativeS23Route.lean`/`NativeObligations.lean` stand
   superseded by the HNet chain — either delete the S23 skeletons
   or docstring-mark them superseded (C4's slice-0 findings 1-2
   give the reasons verbatim).
3. **Standing items unchanged by this unit:** the comparator
   landmark STALE note (≥148 commits, escalated since U8 — the
   operator's judge run at the merge); the two sanctioned no-diff
   notes (fresh-lane worktree, docs+specs-only arcs — no runtime
   change in this lane, ever).
4. **What the lane hands the arc-4/I2 side** (interface premises
   stated here, proofs theirs): `S1CheckerInterface` (C3),
   `S23CheckerInterface` + the anomaly scope note + the
   ENode↔HNode log-convention projection (C4), with
   `appliedLog_prefix_star` provided as the cumulative-record
   justification their premise proof will want.
5. **Assembly seams for the T1 wave:** `EStep` (election) and
   `HStep` (post-election) compose via the S1 output (`ldr`, `tm` =
   the unique leader and its O5b-stable term); `certified` awaits
   the S2-wave match-evidence member (SC1's leaderCommitOk note).

**PROPOSED NEXT CHARTER for this lane:** none — the lane's scoped
program (SC1 probes → C3 native S1 → C4 S2/S3 leaf) is COMPLETE at
this tip; the natural next units (I2 checker-side proofs, the T1
assembly composition, the Verdi family instance) belong to the
arc-4 lane or T1-wave planning per the design of record's phase
structure. Recommend the lane land at the wave boundary and retire
this worktree.
