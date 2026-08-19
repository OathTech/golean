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
  (`GoLean/GoCore/Multi.lean`, ~1.6k lines: `stepMulti`, park/wake,
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
  boundaries (the C2/C3 pins; the registry-path-vs-full-interleaving
  question is NPDRF register #5, with unknowns U-1/U-5 — id corrected
  by audit: U-2 is the L4⊆L1-reachability question, a different
  obligation). Sharper still: the essence-doctrine register #1 records
  an ORACLE-VISIBLE definitional bug in the granularity pin today (the
  send-then-spin wedge — gc exits 0, the machine fuel-outs on every
  stream; observed ∉ modeled), first in the re-envelope queue.
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
  clusters before quantified `num_parties` (audit note: fixed-3/5 is
  the study's recorded LEAN, not part of the user ruling — confirm at
  §8.2).

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
     is narrower than "all Go behaviors" until the NPDRF register #5
     question closes; the statement docstring scopes it honestly or
     the push includes the mover theorem. The register #1 send-then-
     spin wedge is NOT scopable — a conforming behavior the machine
     cannot produce is a definitional bug and must be fixed (it heads
     the re-envelope queue).

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
   the loop under a per-node stop-canceled context;
3. (audit-found, 2026-08-16) restart requires persisting the
   ConfState, not just log entries — `RestartNode` restores membership
   from the snapshot metadata, and a config-less restart is silently
   unpromotable. The harness now persists it and `crash-restart`
   asserts the recovered node regains leadership. The same audit
   hardened the checker itself: S3 re-deliveries surface as recorded
   anomalies, S4 runs even on completion timeout, and per-scenario
   exercise floors make an unexercised S1 fail loudly.

All are recorded in the README as design inputs for the P2 machine
twin — an in-machine harness will face the same ownership,
loop-decoupling, and storage-invariant questions.

## §7 Gap analysis: running the harness family on the machine (2026-08-15)

Surveyed against the pipeline's current support (evidence:
the single-package refusal in `tools/nativefrontend/main.go`;
`docs/2026-07-30_quorum-extern-policy.md`; the method-set/embedding/
generics/defer-panic corpus suites; `docs/coverage-ledger.md`;
`docs/BUGS.md`) and against the raft core's measured import surface
(`go list` over `.`, `quorum`, `tracker`, `confchange`, `raftpb`).

**Layer A — the harness shell (`raftharness/*.go`): a planned rewrite,
not a port.** The shell leans on wall-clock time (`time.Ticker`/
`Sleep`/`After`), `context` budgets, seeded `math/rand/v2` chaos, and
`fmt`/`flag`/`os` reporting — none interpretable, none meant to be.
The P2 twin replaces each with machine-native structure: logical tick
driving; fuel in place of deadlines; **the choice stream in place of
the chaos RNG** — drops/dups/delays/partition schedules become
∀ch-quantified envelope nondeterminism, so each go-run seed witnesses
one envelope member (the two-bounds coherence, exactly). Goroutines,
channels, select, mutex/WaitGroup are already supported; the shell
deliberately uses no atomics (out of scope by design) — keep it that
way.

**Layer B — the raft core (raft.go + quorum + tracker + confchange +
log/storage, ~5.0k lines measured; raft.go itself is 2,162, the whole
module ~7.9k non-test excluding raftpb/rafttest — sizes corrected by
audit): mostly language-feasible today; the blockers are structural,
not semantic.**
- Supported already: interfaces + real method-set records (`Storage`,
  `Logger`, `AckedIndexer`), value/pointer receiver asymmetry,
  embedding (gc-style promotion wrappers), closures, defer,
  panic/recover, generics by monomorphization, maps with struct keys,
  pointers into structs. The measured stdlib surface is small: 8×
  `slices.Sort` (integer elements — the one existing extern), 2×
  `slices.SortFunc` (gap: extend the extern or vendor as source —
  pure generic Go, monomorphizable), 3 non-logger `fmt.Sprintf` in
  raft.go, `strconv`/`strings` only in rendering paths, no `goto`.
- **Blocker 1 — single-package lowering** (the `parser.ParseDir`
  one-package refusal in `tools/nativefrontend/main.go`). The raft
  core spans 5 packages. Either true multi-package lowering (deferred
  from the quorum pilot, requires the BUG-010 package-name TypeId fix;
  the ledger already anticipates it) or a mega-vendor at ~30× the
  pilot's 168 lines. Recommendation: multi-package lowering is the
  honest arc — a whole-library vendor accumulates deltas that erode
  the "real etcd-io/raft" claim the pilot's verbatim discipline
  established.
- **Blocker 2 — the election-jitter seam.** `raft.go` draws its
  randomized election timeout from `crypto/rand` + `math/big` — a
  nondeterminism source *inside the subject*. Doctrinally this is a
  latitude point: model it as a new choice-consumption site
  (∀-quantified, like L1) rather than injecting a pinned rand.
  Needs its own envelope argument in the latitude inventory.
- Logging: `Logger` is an interface — inject a no-op implementation
  (empty bodies, no fmt); rendering/`String()` paths ride the standing
  per-decl quarantine, fail-closed if ever called (the extern-policy
  pattern, unchanged).
- Concurrency-relevant defect state (corrected by pre-merge audit,
  2026-08-16 — the original text called all six "open"): BUG-002
  (expression-step atomicity) and BUG-010 (package-name TypeId) are
  the OPEN ones — BUG-002 needs a disposition before the concurrent
  twin, BUG-010 before multi-package identity. BUG-045/046 (channel
  shadow locations) and BUG-047 (double call emission on
  conversion-of-call) were fixed 2026-08-08; BUG-009 (imported
  method sets) was fixed 2026-08-05.
- P1's discovery instrument is unchanged: stage 4's differential
  against etcd's own datadriven traces will surface whatever raft.go
  hits that the corpus never exercised.

**Layer C — raftpb/protobuf: never interpret it; engineer it out.**
At the current floating rev, `raftpb` drags in `reflect`, `unsafe`,
`sync`, and the protobuf runtime — permanently `deferred-unsafe`
class. Ranked strategy (compose 1 or 2 WITH 3):
1. **Pin `deps/raft` to the last gogo-protobuf rev** (pre-migration):
   raftpb becomes plain reflection-free structs with generated plain-Go
   Marshal/Unmarshal. Rev pin is a user ruling (the pins table records
   raft as deliberately floating; the go-run family would need its
   getter calls reverted to field access).
2. **Or a hand-written `plainpb` shim**: same API surface, plain
   structs. raftpb is generated code, so "same .proto, different
   generator" is a defensible verbatim-ness argument — but it is a
   documented delta either way.
3. **Avoid runtime marshaling entirely** (works under 1 or 2): the
   in-memory network passes structs (no wire encode); MemoryStorage
   stores structs (no persistence encode); the application-side
   `proto.Unmarshal` (ConfChange apply) disappears if membership is
   seeded via a pre-populated snapshot/ConfState instead of
   `StartNode`'s conf-change entries. Marshal/Unmarshal then sit
   quarantined-if-called, never called. **Audit-found residue that
   marshal-avoidance does NOT remove** (all inside Layer B): raft's
   flow control computes protobuf wire sizes on the normal path
   (`entsSize`/`limitSize` → `proto.Size`, callers in storage/log/
   raft/rawnode); `proto.Clone` deep-copies on append/snapshot paths;
   and `stepLeader` has two more `proto.Unmarshal` sites on its
   MsgProp path. Under the gogo pin these are all generated plain Go;
   under `plainpb` a wire-accurate `Size` (or a size-seam with a
   recorded fidelity argument) is an explicit extra obligation — this
   is a real, previously unnamed cost of option 2.
4. Modeling protobuf encode/decode as extern intrinsics is the worst
   option — encoding semantics enter the TCB for no benefit given 3.

**General library policy (the standing one, extended, for the record):**
pure-Go libraries (slices, cmp, sort, errors) vendor as source and
lower like any Go — "no stdlib" is really "no cross-package" until
Blocker 1 falls; impure/runtime-touching packages (reflect, unsafe,
time, crypto, os) are never interpreted — quarantine-unless-called,
replace behind a harness-owned seam, or (only when semantically
necessary) model as a ledgered extern with a differential obligation,
the `slices.Sort` pattern. Time and randomness specifically become
choice sites, not models — they are nondeterminism, and the envelope
is where nondeterminism lives here.

**Net:** the P1 work list, ordered — multi-package lowering (+BUG-010),
`slices.SortFunc`, the raftpb strategy ruling (§8.6), the
election-jitter choice site, no-op logger + quarantine sweep, then
stage-2–4 lowering driven by the datadriven-trace differential. Layer
A costs nothing until P2 and is a redesign, not a gap.

## §8 Open decisions (for user ruling, not urgent)

1. Charter predicate: agreement as end state, KV-linearizability as
   stretch tier (§3.2) — confirm.
2. Tier ladder as completion structure: fixed-3 agreement → ∀n →
   linearizability (§3.3) — confirm.
3. Network envelope for the pinned statement: reliable-first with the
   scope stated, chaos envelope as a later tier (§3.5) — confirm.
4. Sequencing vs the examples lane: P1 touches semantic core +
   `Corpus/` + `baselines/` — serialize or seam. **RESOLVED BY EVENTS
   2026-08-16: the examples campaign landed on `main`; ownership is
   open.**
5. Whether P1 (stages 2–4) runs supervised (recommended here) or gets
   folded into the autonomous push.
6. raftpb strategy: gogo-rev pin vs `plainpb` shim (both with
   marshal-avoidance, §7 layer C) — user ruling needed (it moves a
   deps pin / touches verbatim-ness). **RULED 2026-08-19 — see the
   RULING block below.**

### §8.6 RULING — `plainpb` shim over the gogo-rev pin (Mike, 2026-08-19)

**The ruling: the `plainpb` shim (option 2), composed with
marshal-avoidance (option 3). NOT the gogo-rev pin.**

**Rationale, as given.** The choice is forward-looking. We verify the
logic of the raft that exists NOW, with the wire types *declared*
rather than *generated* — pinning `deps/raft` backward to the last
gogo rev would buy plain-Go `Marshal`/`Unmarshal` at the price of
verifying a library etcd has already moved off. The encode paths are
provably never taken under marshal-avoidance, so declaring the types
costs nothing we were going to exercise, and the restrictions the shim
imposes are liftable later (a wire-accurate `Size`, a real encoder)
without re-deciding this.

**A NOTE THE RULING RESTS ON** (raft-w1, tier-1 probe, `docs/raft-w1-log.md`):
at the pinned rev the runtime is `google.golang.org/protobuf`, not
gogo — raft has *already* migrated. §7 layer C's "pin `deps/raft` to
the last gogo-protobuf rev" therefore means pinning BACKWARD, which is
what the ruling declines.

**Requirements attached to the ruling** (all four are conditions on the
implementation, not suggestions):

- **(a) Mechanically derived.** The shim is produced by STRIPPING the
  actual generated `raftpb` file, and the derivation is a re-runnable,
  documented script, so the delta re-derives when the raft pin moves.
  `scripts/` is off-limits to the lane, so it lives in
  `tools/raftsubject/` (noted here per the ruling).
- **(b) Fail-closed, never silent.** Every runtime-touching method —
  `Marshal`, `Unmarshal`, `Size`, descriptor init/registration — is an
  explicit panic/refusal a differential would see. Never a silent zero.
- **(c) Recorded delta.** Every divergence from the upstream raftpb
  source is itemised in a subject-delta section of the lane log and
  the design note.
- **(d) Differential obligation on real logic.** Any shim method
  carrying real logic (ConfState equivalence; the `Entry`/`Message`
  helpers raft's logic calls) is probed against upstream under
  `go run` and the comparison recorded.

**Implemented by raft lane W2.1** — `raftsubject/raftpb/` (the shim),
`tools/raftsubject/derive.py` (the derivation, requirement a),
`tools/raftsubject/difftest.py` (requirement d), and
`docs/raft-w2-log.md` (requirements b and c: the fail-closed register
and the subject-delta ledger). One requirement is discharged with a
named residue rather than fully: `proto.Size` is a fail-closed stub
today, while raft's flow control computes wire sizes on its NORMAL path
(§7 layer C's audit-found residue). That is not reached by the packages
vendored so far and is the head of W4's obligation list, recorded as
such — not quietly deferred.
