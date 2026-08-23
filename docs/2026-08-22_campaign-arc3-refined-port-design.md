# Arc 3 design: porting verdi-raft's ghost layer (`refined_raft_net_invariant`)

Campaign Arc 3, opening unit (constitution §5 Plan A — the Verdi
STRUCTURE port). Companion log: `docs/campaign-arc3-log.md`. Primary
sources read at their recorded pins: `deps/verdi-raft` @ a3375e8,
`deps/verdi` @ 7e1641b (reference checkouts, read-only). All Coq line
numbers below are at those pins.

## 1. What the ghost layer IS

Verdi's base induction principle (`raft_net_invariant`, ported in
`compat/verdi/VerdiCompat/ProofStructure.lean`) proves invariants of
the REAL node state. But raft's deep invariants are mostly about
history the real state forgets: who voted for whom in past terms, what
a candidate's vote set was when it won, what a leader's log was at
election. Verdi's answer (`deps/verdi/theories/Core/GhostSimulations.v`)
is a GHOST-VARIABLE refinement: run the same protocol, but carry at
each node an extra `ghost_data` component updated by pure functions of
the pre-state on every handler step — history variables in the
Abadi–Lamport sense. The ghost state:

- **never influences execution** — the refined handlers
  (`GhostSimulations.v:26-33`) run the real handler on the real
  component and write the ghost component beside it;
- **is therefore erasable** — `deghost` (`GhostSimulations.v:73-84`)
  projects a refined network to a base network, and the two simulation
  theorems make erasure lossless in both directions:
  `ghost_simulation_1` (`:166-191`, refined step → base step) and
  `ghost_simulation_2` (`:193-232`, base step → some refined step);
- **makes non-inductive invariants inductive** — e.g. "at most one
  leader per term" is not inductive over the real state, but IS a
  consequence of vote bookkeeping that only the ghost state retains.

The raft instance (`deps/verdi-raft/theories/Raft/RaftRefinementInterface.v`)
fixes `ghost_data := electionsData` (`:10-16`), five fields:

| ghost field | type | recorded history | who needs it |
|---|---|---|---|
| `votes` | `List (term × name)` | every vote ever granted, per voter | `votes_correct`, `one_leader_per_term` |
| `votesWithLog` | `List (term × name × List entry)` | the voter's log at each grant | votes-with-log chain (leader completeness side) |
| `cronies` | `term → List name` | a candidate's supporters per term | `cronies_correct`, `one_leader_per_term` |
| `leaderLogs` | `List (term × List entry)` | the log a node held at the moment it became leader | leader-completeness/log-matching chain |
| `allEntries` | `List (term × entry)` | every entry a node ever appended | candidate_entries / allEntries chain |

The update functions (`RaftRefinementInterface.v:18-146`) are keyed to
the handlers: `update_elections_data_requestVote` (a new grant appends
to `votes`/`votesWithLog`), `_requestVoteReply` (a candidate's
`votesReceived` snapshots into `cronies`; a candidate→leader
transition snapshots its log into `leaderLogs`), `_appendEntries` (an
accepted append records `(replyTerm, e)` per entry into `allEntries`),
`_timeout` (a self-vote on becoming candidate), `_client_request` (a
leader's new entry into `allEntries`). Dispatchers
`update_elections_data_net`/`_input` (`:92-101`, `:142-146`) select by
message/input, mirroring `handleMessage`/`handleInput`.

**For the election-safety chain specifically** the load-bearing ghost
variables are `votes` and `cronies` (and `votesWithLog` only as
carried structure): the argument is "a leader won a quorum of cronies;
cronies are votes; votes are unique per term; two same-term leaders
would force a common voter to have voted twice."

On top of the instance sit (`RaftRefinementInterface.v:166-209`,
`:211-325`, `:522-569`):

- `refined_raft_intermediate_reachable` (RRIR) — the refined twin of
  `raft_intermediate_reachable`, closed under refined `step_failure`
  AND the four decomposed handler stages (handleInput, handleMessage,
  doLeader, doGenericServer), ghost updated exactly at the
  handleInput/handleMessage stage and held fixed through
  doLeader/doGenericServer;
- the 11 per-handler obligation shapes
  `refined_raft_net_invariant_*` — same shapes as the base layer plus
  a `gd = update_elections_data_… ` equation premise;
- the interface class: THE principle `refined_raft_net_invariant`
  (obligations → invariant holds of every RRIR network), its primed
  variant, and the four transfer components `lift_prop`, `lower_prop`,
  `deghost_spec`, `simulation_1` — proved in
  `RaftProofs/RaftRefinementProof.v` (633 lines; the principle at
  `:56-194`, `simulation_1` at `:429-496`, `simulation_2` — the
  reghosting construction behind `lower_prop` — at `:507-599`).

The two transfer directions, which the chain files use constantly:

- `lift_prop` (`RaftRefinementProof.v:498-505`): a BASE invariant
  holds at `deghost net` for every RRIR `net` — imports already-proved
  base facts into ghost proofs (e.g. `CroniesCorrectProof.v:16-25`
  lifting `candidates_vote_for_selves`).
- `lower_prop` (`:601-609`): a property proved of `deghost net` for
  every RRIR `net` holds of every base-reachable network — exports the
  ghost-proved conclusion back down. THE transfer principle: this is
  how `one_leader_per_term` (a statement about REAL state only)
  is delivered at base level from ghost-level bookkeeping
  (`OneLeaderPerTermProof.v:58-67`). Its engine is `simulation_2`:
  every base-reachable network is `deghost` of some RRIR network.

## 2. How it re-grounds in OUR vocabulary

Per the compat design note (`docs/2026-08-09_verdi-compat-layer.md`)
§4c/§4e and its §9 translate-don't-certify ruling, as bound into the
constitution's Plan A:

- **compat/verdi is the read-only upstream STRUCTURE reference, never
  an import.** The campaign's T1 statements live over the machine-twin
  harness and the interpreter (§4e: shell node-step DEFINED by
  interpreter-run equations on the pinned lowered `raft.Step`); nothing
  in the T1 statement closure will mention `VerdiCompat`. What
  transfers is the ARCHITECTURE: the invariant decomposition, the
  handler-indexed obligation shapes, the ghost-variable technique, and
  the lift/lower discipline between a ghost layer and the base layer.
- **What this unit ports is structure, not text** (§9: a guided
  re-proof — statements 1:1 against cited source lines, proofs
  re-derived; Ltac does not port). The ported principle is the
  feasibility demonstration + working blueprint: when the harness-side
  proof needs a history variable (and election safety will — the
  harness's real node state forgets exactly what Verdi's does), the
  ghost construction is re-instantiated over OUR step relation with
  the same erasability obligations (`deghost`-simulation both ways),
  not imported from here.
- **Ghost state is a proof device, never a statement dependency**
  (constitution §3.2): `lower_prop` is precisely the discipline that
  keeps it so — every ghost-proved theorem ships its base-level
  projection, and only the projection is ever headline material. The
  ported layer enforces this shape mechanically: `one_leader_per_term`
  is stated over base networks; the ghost appears only in its proof.

## 3. The election-safety chain — file-by-file map

The chain delivering `one_leader_per_term` (verdi-raft's election
safety; the S1 analog). "Interface" files carry the statement,
"Proof" files the instantiation; everything is under
`deps/verdi-raft/theories/` (Raft/ = interfaces, RaftProofs/ = proofs).

| invariant | stated in | proved in (lines) | layer | depends on | becomes here |
|---|---|---|---|---|---|
| `refined_raft_net_invariant` + transfer (`rri`) | Raft/RaftRefinementInterface.v | RaftProofs/RaftRefinementProof.v (633) | — | base principle (ported) | **THIS UNIT**: `RefinedProofStructure.lean` |
| `votes_le_currentTerm` | Raft/VotesLeCurrentTermInterface.v | RaftProofs/VotesLeCurrentTermProof.v (156) | ghost | rri only | unit 2, first instantiation (smallest self-contained) |
| `votes_correct` (3 conjuncts: one vote per term; votes↔votedFor both ways) | Raft/VotesCorrectInterface.v | RaftProofs/VotesCorrectProof.v (249) | ghost | rri, votes_le_currentTerm | unit 2 |
| `candidates_vote_for_selves` | Raft/CandidatesVoteForSelvesInterface.v | RaftProofs/CandidatesVoteForSelvesProof.v (133) | BASE | base `raft_net_invariant` (already ported) | unit 2 (exercises the base principle) |
| `cronies_correct` (4 conjuncts: votesReceived⊆cronies; cronies→votes; RVR-packets→votes; leaders won) | Raft/CroniesCorrectInterface.v | RaftProofs/CroniesCorrectProof.v (718) | ghost | rri, votes_correct, lifted candidates_vote_for_selves | unit 2/3 (the big one) |
| `one_leader_per_term` | Raft/OneLeaderPerTermInterface.v | RaftProofs/OneLeaderPerTermProof.v (73) | BASE via `lower_prop` | rri, votes_correct, cronies_correct, `wonElection_one_in_common` (Raft/CommonTheorems.v) | unit 3 — the chain's exit theorem |

Whole chain: 1,329 lines of Coq proof over the ported principle.
Beyond it (NOT this arc's chain, mapped for orientation): the
leader-completeness side rides `candidate_entries`
(CandidateEntriesProof.v; + cronies_term, term_sanity) and
`leaderLogs`/`allEntries` invariants, ultimately into
`StateMachineSafetyProof.v`; a further msg-ghost layer
(`Raft/RaftMsgRefinementInterface.v`) adds per-packet ghost logs for
the GhostLog* files.

## 4. Porting order for Arc 3

Smallest self-contained chain first, each unit ending buildable +
AxCheck-clean:

1. **This unit**: `RefinedProofStructure.lean` — `electionsData`, the
   update functions, refined params, RRIR, the 11 obligations, THE
   principle, `deghost`/`deghost_spec`, both simulations,
   `lift_prop`/`lower_prop`. Discharge witness: one small concrete
   invariant instantiated through the principle (non-vacuity per
   constitution §3.3; the base file's analog is its use by
   Properties.lean).
2. **Unit 2**: `votes_le_currentTerm` → `votes_correct` →
   `candidates_vote_for_selves` (statement files 1:1; spec-lemma
   helpers from SpecLemmas.v/RefinementSpecLemmas.v ported on demand,
   only the ones actually used).
3. **Unit 3**: `cronies_correct`, then `one_leader_per_term` +
   `wonElection_one_in_common`. Exit: election safety at the base
   layer, entirely inside compat/verdi.
4. **Later arcs** (not Arc 3): candidate_entries/leaderLogs chain,
   msg-ghost layer, state-machine safety.

## 5. Design decisions (recorded per the capture rule)

- **D1 — raft-specific, not generic.** We inline Verdi's generic
  `GhostMultiParams` construction at its raft instance rather than
  porting `GhostSimulations.v`'s typeclass layer: one ghost instance
  in scope this arc; the Coq generic layer's payoff (TotalMapSimulations
  reuse) is machinery we are not porting — both simulation proofs are
  direct inductions in Lean regardless. Lift to a generic layer when a
  second instance (msg-ghost) arrives. (Log entry 2026-08-22.)
- **D2 — obligation statements 1:1, constructor premises Lean-native.**
  The 11 obligation defs keep Coq's premise shapes exactly (explicit
  `gd` with equation premises) because they are the interface ~73
  proof files instantiate. RRIR constructors use pair projections
  where Coq threads `nwState net h = (gd, d)` equations (definitional
  pair eta makes these interchangeable), matching the base port's
  already-recorded style for `RIR_doLeader`.
- **D3 — interface classes dissolve.** Coq's
  `raft_refinement_interface` class exists to break a module cycle
  (interfaces usable before the proof compiles). We prove the
  principle directly in the defining file, as the base port did; chain
  files will cite theorems, not class fields.
- **D4 — primed variants deferred** (GAP-1 in the log): the `…'`
  obligations add a post-state-reachability premise used by a minority
  of chain files; known-shape repeat, ported when first needed.
- **D5 — deghost across definitionally-equal packet types.** The
  refined and base `Packet`/name/msg types are distinct instantiations
  with identical component types; `deghost_packet`/`ghost_packet` are
  the explicit isos (round trips definitional by structure eta). This
  mirrors Coq's `deghost_packet`/`ghost_packet` rather than trying to
  make the types coincide — keeping the two layers visibly distinct is
  what keeps "ghost never in a statement" checkable.

## 6. CLOSING SECTION — the port's final extent (2026-08-23, unit 16)

The arc ran sixteen units on the `campaign-arc3` lane and CLOSED THE
FULL T3 SAFETY LATTICE: **election safety** (unit 2, base),
**log matching** (unit 6, base), **leader completeness** (unit 10,
refined — upstream's own landing point), **state-machine safety**
(unit 15, base). All three `Properties.lean` transfer targets
(`OneLeaderPerTermStatement`, `LogMatchingStatement`,
`StateMachineSafetyStatement`) are discharged natively, per this
note's §2 translate-don't-certify conditioning. ~80 upstream proof
files (~30k upstream lines) are ported across sixteen campaign
modules; the running INVARIANT INDEX in `docs/campaign-arc3-log.md`
maps every row to its Interface file and its Lean home.

**Ported vs re-derived vs newly-shaped.** Statements are 1:1 against
their Interface files at the pin, always. Proofs divide into three
honesty classes, each marked at its site:

- *Ported* (the default): the same lemma DAG as upstream, re-proved —
  Ltac does not port, the argument does.
- *Re-derived routes* (the logged §9 calls — same lattice inputs,
  smaller arguments), the majors: unit 10's `aeae_e_in_ll` positioning
  lemma (~170 Lean lines for upstream's ~590-line 3×3 grid); unit 8's
  two containment lemmas replacing AllEntriesLog's ~500-line AE Ltac;
  unit 13's Q-ROUTE for the primed principles (derive from the
  unprimed principle at `Q net := reachable net → Pr net` — twice, msg
  then state side, no staged induction duplicated); unit 14's two
  SMS-prime cores; unit 15's GAP-8 reghosting DIRECTLY through the
  packet-subset reachability constructors (upstream's dup-drop
  step-star detour never enters); unit 15's watermark and survival
  cores factoring upstream's four duplicated ~90-120-line AE bullets
  each into one lemma; slice 39's pre-state route through
  `one_leaderLog_win_host` (which deferred GAP-1 by five units until
  MatchIndexAllEntries genuinely needed the primed premise).
- *Newly-shaped* (no upstream counterpart): the constructive
  replacements the enforcing axiom sweep forced (`eraseOne`, the
  pigeon layer, `sorted_mem_eq`, `moreUpToDate_elim`), the
  `_of_update` transport-lemma idiom replacing upstream's
  `update_destruct; rewrite_update` Ltac, and the unit-16
  consolidation (`update_proj_mem`; term-level→entry-level
  candidateEntries derivation).

**T4 (linearizability) was explicitly NOT attempted.** The
constitution (§2.3) marks it a stretch tier; `Linearizability.lean` /
`RaftLinearizable.lean` remain P1 STATEMENT ports, and their proof
chain (`RaftLinearizableProofs.v` and the client/output cluster) is
unported. Nothing in the lattice pre-commits against it — the ghost
layers and both transfer principles it would ride are proved.

**The handoff surface for the Arc-4 seam: THE INDEX IS THE
INTERFACE.** The INVARIANT INDEX (84 rows, span-verified each unit) is
the complete map of what exists: a consumer names a row, cites the
Interface file for the statement, and imports the Lean home. Per §2 of
this note, `compat/verdi` remains a read-only structure reference for
the harness-side campaign — the T1 statements never import it; what
crosses the seam is the architecture (the invariant decomposition, the
obligation shapes, the ghost technique, the lift/lower discipline),
re-instantiated over the interpreter's step relation. The lane ends
BRANCH-COMPLETE; merge, designation, and the comparator-judge run
belong to the operator's queue.
