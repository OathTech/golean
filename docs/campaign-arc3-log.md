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
