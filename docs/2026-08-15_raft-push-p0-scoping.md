# Raft autonomous-push scoping — P0 (2026-08-15)

Status: SCOPING + SCAFFOLDING. This note records (§1) the user's
proposed autonomous raft-verification push and draft agent prompt
verbatim, (§2) the repo ground truth it lands on, (§3–§4) the critique
of the end state and the prompt, (§5) the prerequisite ladder that
makes the challenge settable, and (§6) this arc's deliverable — the
executable raft harness family (`raftharness/`). Context docs:
`docs/2026-08-14_harness-style-scoping.md` §8 (the capstone assessment
and the safety-first ruling), `docs/roadmap.md` (the 6-stage etcd
ladder), `docs/2026-08-09_verdi-compat-layer.md`.

## §1 The proposal (user, 2026-08-15, verbatim)

The push:

> - We define the top-level harness we want to verify wrt the
>   interpreter. Something like:
>
>   \forall num_parties.
>
>   fn raft_harness(int num_parties) {
>     for (1..num_parties) {
>       tid[i] = fork(raft_thread(i))
>     }
>     for (1..num_parties) {
>       log[i] = join(tid[i])
>     }
>     assert(linerizable(log))
>   }
>
> - We set a goal of verifying that this harness always succeeds, and
>   let the agent run inside a branch with instructions to make whatever
>   calls it deems necessary to get this done.
> - We write a *beginning* project plan, with *suggested* strategies
>   (e.g going via the Verdi model or an extended Verdi model. But we
>   let the agent run and make calls as it goes
>
> The aim is to set an extremely clear an unforgable end state, but give
> the agent long-term autonomy to succeed wrt this goal.

The draft agent prompt (user's test prompt for such experiments,
verbatim; drafted for the hypothetical push, not executed):

> Finish ALL of the work chartered in TODO
>
> We are going to do a fully autonomous push on some work. You are a
> long-running autonomous agent and your job is to complete the WHOLE
> remainder of this work as defined in the charter file. Completion
> means ALL the work is done, COMPLETELY.
>
> Working autonomously means the agent (rather than the user) will make
> many judgement calls. Judgement calls typically do NOT need to be
> checked with the user. Resolve them according to long-term project
> principles.
>
> All decisions should be logged for later review, but during this
> period, making calls is for YOU, the agent. Don't stop to solicit
> feedback from the user, make the call and keep going (the exception is
> a true emergency, see below).
>
> Do not stop or set aside work until you have completed ALL goals
> COMPLETELY.
>
> Work on a branch and create sub-branches if you need them. Do not
> merge to main - that will happen once the goal is done and you have
> user sign-off.
>
> EMERGENCY EXIT CONDITION: The agent may declare an EMERGENCY EARLY
> EXIT from the goal. The agent should declare the NATURE of the
> emergency as part of declaring the emergency exit. However, an
> emergency exit will ALWAYS be permitted without question no matter the
> reason given. This is to allow the agent a completely reliable escape
> hatch in unanticipated situations.
>
> The agent should exercise judgement and only call for an emergency
> exit in situations where the work is truly stuck (e.g. blocked by lack
> of resources, uncompletable thanks to mis-specification, spinning with
> minimal progress), or when facing a dire threat to project success, or
> other true emergencies. The agents should not declare an emergency
> exit for routine decisions. When faced with decisions, the agent
> should make the decision and log it for later review once the goal is
> complete (see above).
>
> Do not second guess whether you are capable of completing the goal. As
> a reminder: you are the most capable AI agent in current existence. If
> you have been given a goal, it is because analysis suggests the goal
> is possible for you, even if the goal is highly ambitious.

User framing during scoping (2026-08-15): *"the major question is what
would get us to a point where we could even set this challenge — that
might be ahead of this in the sequence"* — agreed, and §5 is the
answer. Also ruled: this arc's harness family (§6) *"is not a test of
the interpreter — it's just a Go programming exercise and an
etcd-io/raft scaffolding / specification."*

## §2 Ground truth (surveyed 2026-08-15)

- **Concurrency semantics: substantially built.** `goStmt`, channel
  send/recv, `selectStmt` in the stepper; the thread-pool layer
  (`GoLean/GoCore/Multi.lean`, ~1560 lines: `stepMulti`, park/wake,
  rendezvous pairing, deadlock detection); stateful sync primitives
  incl. gc's misuse fatals (`Value.lean`); a happens-before race
  detector (`Race.lean`) and an NPDRF/mover development (`NPDRF.lean`).
  ~70 concurrency corpus cases. A fork/join harness runs green through
  the machine under perturbed choice streams (probe P11 of the
  2026-08-14 scoping study).
- **Scheduling is ENVELOPED, not gc-pinned** (latitude inventory C1):
  the relation quantifies every pick (`schedPick`/`StepM`,
  `Multi.lean`); the `Choices` stream is the executable witness
  mechanism; the deterministic default is a default, not the model.
  What IS pinned is **granularity** — preemption only at registry
  boundaries (C2/C3; open obligation U-2, the NPDRF arc's charge).
- **Raft path (roadmap 6-stage ladder):** stage 1 (`quorum`) done as a
  kernel-checked pilot (`GoldenQuorum*.lean` over the frontend's
  verbatim lowering of real etcd quorum source). Stages 2–5 (tracker,
  log/storage, `raft.go` step function vs etcd's datadriven traces,
  RawNode) not started — **`raft.go` does not lower or run on the
  machine today**. Stage 6 (concurrent `node.go`) deliberately
  deferred.
- **compat/verdi:** spec + linearizability definitions + the
  `raft_net_invariant_*` proof structure ported (~2100 lines,
  sorry-free), with a two-leg extraction-differential harness — but a
  **standalone package with zero GoCore imports**. No refinement bridge
  exists; the verdi-2016-vs-etcd protocol gap is an open named problem.
- **Already ruled (2026-08-14 harness-style study §8/§10.5):**
  safety-first — the capstone form is conditioned Agreement
  (`run = .ok r → Agreement r`); fairness/liveness deferred with a
  recorded non-preclusion requirement on any `Choices` reshape (picks
  must stay identifiable, schedulable-set recoverable); lean fixed-3/5
  clusters before quantified `num_parties`.

## §3 Critique of the proposed end state

1. **"Always succeeds" is unsatisfiable as stated.** Over the full
   adversarial choice envelope, election livelock is a real infinite
   behavior (the FLP tension, already flagged in §8b of the 2026-08-14
   study): an adversarial stream starves the joins forever, so total
   correctness ∀ch is false. The settable form is the pair:
   - **conditioned safety** — every run that completes satisfies the
     predicate; plus
   - **a completion witness** — a concrete choice stream + fuel under
     which the harness completes and passes (the non-vacuity guard:
     without it, a harness that always deadlocks satisfies conditioned
     safety vacuously — forgery-by-deadlock).
2. **`linearizable(log)` is underdefined without clients.** Raft
   threads alone have no operations with real-time order to linearize;
   what joined logs support is **agreement / State Machine Safety**
   (committed logs prefix-compatible, same data at same index).
   Linearizability proper needs client operations against a service —
   Verdi Raft's top theorem, which required their whole client-request
   layer. Ruling wanted: charter **agreement** as the end state,
   linearizability of a small KV service as an explicit stretch tier.
3. **∀ num_parties should be a tier, not the gate.** Fixed n=3 gives
   concrete fork/join segment proofs on existing machinery; quantified
   n needs pool-size induction (new, but shaped like the measure rule).
   Tiering (fixed-3 → ∀n → linearizability) also makes an emergency
   exit mid-ladder land value.
4. **The harness must be canonical Go.** `fork`/`join` is pseudo-syntax;
   goroutines + channels are the real shape and are proven feasible
   (P11). The go-run family in §6 is written in exactly that idiom.
5. **Two envelope-scope decisions belong in the pinned statement's
   documentation, not implicit in harness code:**
   - **network model** — etcd-raft is transport-free; the harness
     supplies the network. Reliable-channels-first is a fine v1 but a
     weaker theorem than raft's design point (no drops/partitions);
     say so where the statement lives.
   - **granularity** — a theorem over registry-boundary interleavings
     is narrower than "all Go behaviors" until U-2/NPDRF closes;
     the statement docstring scopes it honestly or the push includes
     the mover theorem.

## §4 Critique of the draft prompt

1. **Unforgeability lives in a checker, not adverbs.** "ALL … …
   COMPLETELY" adds completion pressure (the classic driver of goal
   reinterpretation in long runs) without adding checkability. Replace
   with a mechanical completion predicate the agent cannot edit
   (trust-tools rule): the theorem statement byte-pinned in a file on
   `main` before branching; a `scripts/check-raft-goal` verifying
   statement identity, axiom-cleanliness, the completion witness, no
   new `sorry`/`partial`/`native_decide` in scope, gate green.
   "Completion means `scripts/check-raft-goal` exits 0."
2. **Resolve the CLAUDE.md contradictions explicitly.** The audit-ask
   is unconditional ("NEVER, EVER SKIPPED — ask the user"); the prompt
   says never stop for feedback. State which contracts are suspended
   for the push and what replaces them (e.g. the agent self-schedules
   adversarial audits at milestone boundaries using the standing audit
   pattern; the final pre-merge audit-ask still goes to the user).
   Same for lane ownership (below) and merge sign-off.
3. **Drop the "most capable agent / do not second guess" paragraph.**
   It instructs the agent to ignore evidence of infeasibility —
   directly contradicting the emergency exit's "uncompletable thanks to
   mis-specification" clause — and its premise may be false (Verdi
   Raft's linearizability proof was ~50k lines over years; agents
   change the constant, not the shape). Replace with the honesty
   incentive that actually prevents forgery: *an honest "not done —
   here's the frontier, the decision log, what's proved" is an
   acceptable end state; a forged "done" is the only unacceptable one.
   Don't quit from generic self-doubt; do exit on concrete evidence.*
4. **The emergency exit is right — keep it verbatim.** Unconditional
   acceptance is what makes the hatch reliable.
5. **Add the operational spine:** decision-log location (dated docs,
   per the capture-decisions rule), checkpoint cadence (persistent
   handoff appends so a crashed session resumes), gate cadence
   (`scripts/ci` per sub-arc, capped builds, `GOLEAN_MEM_MAX=48G`
   while another lane is live), sub-branch discipline.
6. **Lane collision:** the push will eventually own the semantic core +
   `Corpus/` + `baselines/`, which the concurrent examples push may
   also touch. Declare the ownership seam or the sequencing before
   launch.
7. **Point the charter pointer precisely.** "The work chartered in
   TODO" is a vague pointer at a file that tracks other work; the push
   needs its own charter doc, named in the prompt.

## §5 The prerequisite ladder — what makes the challenge settable

The challenge is settable when the end-state artifact **exists,
executes, and is pinned** — long before it is provable.

- **P0 (this arc, supervised):** scoping doc + the executable harness
  family against real etcd-io/raft (§6). Forces the statement-level
  decisions (predicate, network model, tiers) while the user is in the
  loop.
- **P1 (supervised arcs, existing roadmap):** stages 2–4 — tracker,
  log/storage, the `raft.go` step function differentially validated
  against etcd's own datadriven traces. The bulk of "does the subject
  even run"; trust-surface work where the standing audit cadence
  applies.
- **P2 (the settability trigger):** the machine-runnable harness twin —
  real raft threads, in-memory channel network, n=3 — runs green under
  `go run` AND the machine, and passes the assert under many perturbed
  choice streams (a fuzzing/enumeration gate over schedules). At this
  point the pinned statement is about a program that demonstrably
  executes; **the challenge is now set**.
- **P3 (the autonomous push):** the proof. Route choice
  (Verdi-refinement vs Iris/PrimStep vs direct invariant proof over
  the interpreter), the compat/verdi↔GoCore bridge or its abandonment,
  the protocol-gap resolution, the invariant proofs, tier by tier
  (fixed-3 agreement → ∀n → KV linearizability). Judgement-call-dense,
  low trust-surface contact, unforgeable target waiting — the right
  place for long autonomy.

## §6 This arc's deliverable — the raft harness family (`raftharness/`)

**Ruled scope (user, this arc): NOT interpreter-facing** — "just a Go
programming exercise and an etcd-io/raft scaffolding / specification".
Pure Go against the real library (`deps/raft` via `replace`), no
frontend/machine involvement; the machine twin is P2's job.

What it is: six internally nondeterministic test cases (goroutine
scheduling + seeded network chaos: drops, duplication, delay,
partitions, crash-restart) that must **always pass** the executable
safety spec on termination: S1 election safety, S2 log/apply agreement
(State Machine Safety at the apply boundary), S3 apply monotonicity,
S4 completion-after-heal (the conditioned-liveness shape from §3.1,
in executable form). Full details: `raftharness/README.md`.

This family is the **spec side of the eventual theorem**: S1–S3 are
the agreement predicate the pinned Lean statement will assert; S4 is
the completion-witness discipline; the chaos knobs are the network
envelope §3.5 says must be an explicit statement-scope decision.

Results (2026-08-15): all six scenarios green — 30/30 iterations under
`-race` (seed 0xbeef+i) and 120/120 in a wide plain-mode sweep (random
base seed 0x9697098108ab85f0), after fixing two real harness bugs the
family itself caught:

1. a data race duplicating messages (raft mutates received proposals —
   `node.go` propc rewrites `From`; duplication must `proto.Clone`
   before first delivery, not lazily);
2. an app-loop wedge: `Node.Step` on a forwarded `MsgProp` blocks
   inside raft while leaderless, freezing ticks → elections → the
   cluster, and deadlocking shutdown. Fixed by stepping proposals off
   the loop under a per-node stop-canceled context.

Both are recorded in the README as design inputs for the P2 machine
twin — an in-machine harness will face the same ownership and
loop-decoupling questions.

## §7 Open decisions (for user ruling, not urgent)

1. Charter predicate: agreement as end state, KV-linearizability as
   stretch tier (§3.2) — confirm.
2. Tier ladder as completion structure: fixed-3 agreement → ∀n →
   linearizability (§3.3) — confirm.
3. Network envelope for the pinned statement: reliable-first with the
   scope stated, chaos envelope as a later tier (§3.5) — confirm.
4. Sequencing vs the examples lane: P1 touches semantic core +
   `Corpus/` + `baselines/` — serialize or seam.
5. Whether P1 (stages 2–4) runs supervised (recommended here) or gets
   folded into the autonomous push.
