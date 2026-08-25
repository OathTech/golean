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
