# Raft master plan: to a statable theorem over a trusted interpreter (2026-08-15)

Status: PLAN OF RECORD for the pre-push phase. This plan covers
everything between today and the moment the raft theorem can be
**stated** — pinned, about a program that demonstrably executes, over
an interpreter whose relevant semantics carry explicit confidence
arguments. It deliberately does NOT cover proving the theorem (the
autonomous push, P3 of `docs/2026-08-15_raft-push-p0-scoping.md`) —
this plan's end state is the push's *starting gun*.

Companions: the P0 scoping doc (ibid.: the ladder, the critique, the
§7 gap analysis, the §8 open decisions), `docs/roadmap.md` (the
6-stage etcd ladder this plan absorbs as W4),
`docs/2026-08-14_harness-style-scoping.md` §8 (capstone form rulings) (branch park/reasoning-2026-08-31).

## §0 The end state, exactly

All of the following, simultaneously:

1. **A pinned Lean statement** — conditioned agreement over a fixed
   3-node cluster harness (`run = .ok r → Agreement r`) plus its
   completion-witness twin (∃ stream+fuel completing and passing) —
   elaborating against the machine vocabulary, byte-pinned in a
   tracked file, with `scripts/check-raft-goal` verifying statement
   identity, axiom cleanliness, witness presence, and gate greenness.
2. **The subject executes**: the harness program (real etcd-io/raft
   core, RawNode-driven, in-machine network) runs green under `go run`
   AND the machine at n=3, and holds its safety asserts under a
   recorded battery of perturbed choice streams.
3. **The interpreter earns the statement** per the §1 confidence
   checklist — each item either discharged or explicitly scoped into
   the statement's documentation.

Tier ladder above this base (pinned as statement variants, not
blockers): quantified num_parties; KV-service linearizability.

## §1 "Confidence in the interpreter", made checkable

The theorem is only as good as the machine under it. Confidence =
this checklist, each item with a named artifact:

- **C-A Differential lower bound.** The raft-shaped corpus is green:
  the go-run harness family (`raftharness/`), the stage-4 datadriven
  trace differential (W4), and the machine-twin corpus cases (W5).
  Artifact: baseline entries + trace-suite record.
- **C-B Envelope upper bound.** Every choice site the statement's ∀ch
  quantifies has a latitude-inventory entry argued against spec text —
  including the NEW sites this plan creates: election-timeout jitter
  (W3.1), network chaos draws (W5.2). Artifact: latitude-inventory
  entries at the standing dossier bar. (Audit correction: the G3
  dossier campaign is SEQUENTIAL-only with a fixed 22-item
  denominator — C-series concurrency sites are explicitly out of its
  scope, so new sites reuse its process pattern and bar, not its
  table.)
- **C-C Granularity honesty.** Two obligations, corrected by audit
  (the original text cited "U-2", which is the L4⊆L1-reachability
  question — a different item). (i) The register #1 send-then-spin
  wedge is an ORACLE-VISIBLE definitional bug in the granularity pin
  (gc exits 0; the machine fuel-outs on every stream) — under the
  two-bounds charter it is NOT scopable and must be FIXED, at the
  head of W3.2's re-envelope queue. (ii) The residual
  registry-path-vs-full-interleaving question (NPDRF register #5;
  unknowns U-1/U-5) then either closes via the mover theorem or the
  statement's docstring scopes the claim explicitly — either is
  honest; silence is not. Artifact: the wedge fix + the register #5
  ruling (W3.3).
- **C-D Concurrency defect clearance.** BUG-002 (expression-step
  atomicity) — the one OPEN concurrency-bearing defect — resolved or
  argued non-bearing on the harness's operation set. (Audit
  correction: BUG-045/046, the channel shadow locations, and BUG-047
  were fixed 2026-08-08; the original text called them open.)
  Artifact: the BUG-002 disposition cited in the statement's
  docstring.
- **C-E Fail-closed subject coverage.** Nothing the subject exercises
  is silently approximated: every stdlib shim carries the G2.E5-style
  fidelity argument + oracle rows (go run executes the REAL function,
  the machine the shim — every row a fidelity test); every quarantined
  path in the vendored/lowered subject is load-tested to be dead
  (called ⇒ visible red). Artifact: shim ledger entries + a
  quarantine-reachability note for the subject.
- **C-F Statement TCB.** The Agreement predicate is defined from base
  definitions over the interpreter (first-order readout, no Iris in
  the statement), with a non-vacuity witness, per the standing TCB
  doctrine. The pre-merge audit protocol applies to every arc here —
  the semantics dimension always audited.

## §2 Ground inputs (what already exists, 2026-08-15)

From the P0 survey and a read-only look at the concurrent lanes:

- Concurrency semantics built and ENVELOPED at the scheduler
  (`Multi.lean`, `schedPick`/`StepM`); granularity pinned (U-2 open).
- Sequential Go deeply covered: interfaces + method-set records,
  embedding via promotion wrappers, closures, defer/panic/recover,
  generics by monomorphization. Single-package lowering only;
  stdlib = `sync` modeled + `slices.Sort` extern.
- **The stdlib-shim mechanism exists** (gallery campaign G2.E5,
  `stdlibshim.go`): allowlisted pure stdlib functions injected as
  synthetic source pre-typecheck, fail-closed, differentially
  fidelity-tested. This is the library strategy's tool — raft's
  `slices.SortFunc` and `errors.New` ride it rather than new
  mechanisms. (Audit caveat: the allowlist is currently ONE entry
  with a direct-call-shape restriction, and shim bodies must stay
  inside the modeled subset — `fmt.Sprintf`'s variadic `any` +
  format verbs may exceed it; the fallback for surviving `fmt` needs
  is recorded-delta trims or hand-rolled formatting, per the
  quorum-pilot pattern.)
- **The latitude census is being closed** (gc-dossiers: 22/22 dossiers,
  ruling table) — new choice sites have a ready process and bar.
- **The re-envelope ruling stands** (channel-logic lane, parked
  2026-08-11 by user ruling): machine re-envelope PRECEDES further
  concurrency proof slices. The parked lane also holds substantial
  concurrency proof machinery (wpDM law ports, the chanInv resource
  tier, a compositional fork/channel flagship) — a running start for
  P3, and a re-proof constituency the re-envelope arc must not break.
- `raftharness/` (this lane): the executable spec family, green.
- The examples campaign owned `Corpus/`, `baselines/`, and gate
  scripts while this plan was drafted — **landed on `main` 2026-08-16;
  the constraint is lifted** (see the §5 addendum).

## §3 Workstreams

**W1 — Frontend capability.**
1. Multi-package lowering: import resolution + qualified identity
   across packages. Prerequisite fix: BUG-010 (TypeId keyed by
   package name → import path). (Audit correction: BUG-009, imported
   method sets, was fixed 2026-08-05 — not a prerequisite.) This is
   the deferred-from-quorum-pilot arc, and the largest single
   frontend item.
2. `slices.SortFunc` (shim or extern extension — decide by fidelity
   argument; shim preferred, it needs no GoCore change).
3. Sweep raft.go stage-by-stage for lowering refusals (W4 drives
   discovery; refusals become either features, shims, or recorded
   subject deltas — never silent).

**W2 — Subject engineering (can start now; no core ownership).**
1. The raftpb ruling (scoping §8.6): gogo-rev pin vs `plainpb` shim —
   user decision, then implement with marshal-avoidance (struct-passing
   network, struct-storing MemoryStorage, snapshot-seeded membership so
   no ConfChange unmarshal ever runs).
2. No-op `Logger` injection; verify rendering paths are
   quarantine-dead under the harness.
3. The machine-twin harness design: RawNode-driven node loops (no
   node.go / context / time), logical tick schedule from the choice
   stream, in-machine channel network, the executable Agreement
   checker as harness Go (S1 verdict fold or S3 relational return —
   decide at pin time against the harness-style study's criteria).
   The go-run family's two found bugs (proposal-mutation ownership,
   MsgProp loop-wedge) are standing design inputs: the twin uses
   drop-and-retry proposal semantics rather than blocking forwarding.

**W3 — Semantics & envelope (semantic-core ownership; serialized).**
1. Election-jitter choice site: raft's randomized election timeout
   (crypto/rand + math/big at the current rev) becomes a modeled
   choice-consumption site with a latitude entry — the subject's own
   nondeterminism joins the envelope. (Seam options if modeling is
   deferred: inject a rand source in the vendored subject — a recorded
   delta.)
2. **The re-envelope arc** (the standing prerequisite ruling): reshape
   `Choices` for the widened concurrency envelope, honoring the
   2026-08-14 fairness non-preclusion requirement — scheduling picks
   identifiable, schedulable-set recoverable (a future
   `Fair : Choices → Prop` must be definable; no flattening). This
   arc unblocks BOTH the raft push and the parked channel-logic lane;
   it carries a re-proof wave (gallery + channel-logic machinery) and
   the strictest audit bar in this plan.
3. The granularity work per C-C: the register #1 wedge fix (heads the
   re-envelope queue), then the register #5 ruling (close via
   mover/NPDRF or scope the statement); the BUG-002 disposition
   (045/046/047 already fixed).

**W4 — Sequential subject validation (roadmap stages 2–4).**
Tracker → log_unstable/MemoryStorage → the raft.go step function,
each stage differentially validated; stage 4's instrument is etcd's
own datadriven traces (`deps/raft/testdata/`), replayed through a
single-file driver on both sides (go run vs machine). Corpus cases
promoted per stage; baseline re-pins deliberate and dated. This is
where the subject's unexercised-path risk is burned down.

**W5 — The concurrent twin (P2 proper).**
1. n=3 cluster harness in canonical Go through the real pipeline
   (P11 shape, scaled): RawNode loops as goroutines, channel network.
2. Network chaos as envelope: drops/dups/delays/partition schedules
   drawn from the choice stream (new latitude entries per C-B) — the
   go-run family's seeded RNG becomes the witness-member generator,
   giving the exact two-bounds correspondence (each seed ↔ one
   stream).
3. The schedule-fuzzing gate: a recorded battery of perturbed streams
   under which the safety asserts hold and at least one recorded
   stream completes (the future completion witness's executable twin).

**W6 — Statement & pinning.**
1. User rulings OBTAINED and folded in (audit correction: these are
   the scoping doc's §8 open decisions — recommended, not yet ruled):
   Agreement as the base predicate (linearizability = stretch tier),
   tier ladder, network-envelope scope statement, raftpb strategy.
2. Elaborate the statement against machine vocabulary (the
   `capstone_safety_shape` scratch form is the seed); write the
   Agreement predicate at statement-TCB level; draft the completion
   witness statement.
3. Pin on `main`: statement file + `scripts/check-raft-goal` +
   docstring carrying the C-B/C-C scope notes. Pre-merge audit, then
   the challenge is set.

## §4 Milestones (checkable exits, roughly in order)

- **M1 — the library runs.** Raft core lowers (W1.1 + W2 done); a
  single-node, tick-driven smoke case is green in the corpus.
- **M2 — the stepper is validated.** Stage-4 datadriven differential
  green over etcd's trace suite; recorded + baselined. (C-A's core.)
- **M3 — the cluster executes.** The n=3 twin green under both
  oracles; fuzzing gate recorded. (P2 of the ladder; C-A complete.)
- **M4 — the envelope is argued.** Re-envelope arc landed; latitude
  entries for jitter + network sites filed; U-2 ruled; bug
  dispositions recorded. (C-B/C-C/C-D.)
- **M5 — the statement is pinned.** W6 complete, audit passed.
  **The challenge is set**; the autonomous push can be chartered.

M1/M2 need only W1+W2+W4. M4 (re-envelope) can proceed in parallel
lanes-permitting since it touches the semantic core, not the frontend
— but see §5. M5 waits on everything.

## §5 Sequencing & lane ownership

**ADDENDUM 2026-08-16: the examples campaign LANDED on `main`** — the
serialization constraint below is lifted by events. Corpus, baselines,
and semantic-core ownership are open; the re-envelope arc (W3.2) can
be scheduled as the next core-owning lane. Original text kept for the
record:

- **Now, without core ownership:** W2 (subject engineering — this
  lane), W6.1–.2 drafting, the raftpb ruling.
- **Semantic-core / Corpus / baselines serialization:** the examples
  campaign currently owns Corpus, baselines, and gate scripts. W1's
  corpus waves and W3's core edits queue behind its landing (or an
  explicit seam ruling). The re-envelope arc (W3.2) is the single
  most contended item — it also unblocks channel-logic; schedule it
  as its own lane, early, with the audit bar and both re-proof
  constituencies budgeted.
- Worktree discipline unchanged; parallel full gates stagger or set
  `GOLEAN_MEM_MAX=48G`.

## §6 Effort shape (arcs, honest ranges)

W1: 2–3 arcs (multi-package is the bulk). W2: 1 arc. W3: 2–4 arcs
(re-envelope dominates; its re-proof wave is the variance). W4: 2–4
arcs (stage 4 dominates; trace-suite breadth is the variance). W5:
1–2 arcs. W6: 1 arc + audit. Critical path: W1.1 → W4 → W5 → W6,
with W3 joining before M4. Nothing here assumes the push's autonomy —
these are supervised arcs under the standing merge/audit protocol
(P0 ladder recommendation unchanged).

## §7 Risks, pre-registered

1. **raft.go scale surprises** (measured: raft.go is 2,162 lines, the
   full lowering target set ~5.0k — audit-corrected from "≈11k") —
   mitigated by stage-wise lowering with the trace differential as
   the discovery instrument and quarantine keeping gaps visible.
2. **Re-envelope breakage** of existing proof estates — mitigated by
   budgeting the re-proof wave explicitly (gallery + parked
   channel-logic), the fairness non-preclusion requirement already
   recorded, and the audit bar.
3. **U-2 turns out load-bearing** for raft-shaped interleavings —
   mitigated by the C-C either/or: honest statement scoping is an
   acceptable M4 exit; the mover theorem upgrades it later.
4. **Protobuf strategy churn** — mitigated by marshal-avoidance
   making both options small and reversible.
5. **Two-lane contention** — RETIRED for the examples campaign (landed
   2026-08-16, §5 addendum); the principle stands for any future
   concurrent core-owning lane: serialize — the cost is weeks, a
   Corpus/baseline merge conflict with laundered re-pins costs trust.
6. **Statement drift during the long middle** — mitigated by drafting
   the statement EARLY (W6.2 can elaborate against today's vocabulary
   with `sorry` proofs, as the scoping study did) and re-elaborating
   at each milestone; the pin at M5 is a re-confirmation, not a first
   contact.
