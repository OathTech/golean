# raftharness — the raft harness family (P0 scaffolding)

A family of internally nondeterministic Go test cases that drive the
**real etcd-io/raft library** (`deps/raft`, via a `replace` directive)
through an in-memory chaos network and assert raft's safety properties
on termination. Every member must pass on **every** run — under every
goroutine interleaving, chaos schedule, and seed.

**What this is:** a Go programming exercise, etcd-io/raft scaffolding,
and the executable *specification precursor* for the raft verification
push (`docs/2026-08-15_raft-push-p0-scoping.md`).

**What this is NOT:** interpreter-facing. Nothing here runs through the
golean frontend or machine. The machine-runnable TWIN exists since W4.2:
`tools/raftsubject/twin-lib.go` (+ the `twin-*-main.go` runners) — n
RawNodes, no goroutines/clock/context, the network as a multiset, this
family's `checkSafety` reshaped to per-step form, schedules as the input,
run under both `go run` and the machine (`docs/raft-w42-log.md` item 2).
This family stays the concurrent, wall-clock, chaos-network EXECUTABLE
SPEC the twin is a twin OF — same properties, different mechanism
(`docs/2026-08-20_machine-twin-harness-design.md` §1).

## Run

```
cd raftharness
GOCACHE="$PWD/../artifacts/go-build-cache" go run . [-scenario all|<name>] [-seed N] [-iters K]
GOCACHE="$PWD/../artifacts/go-build-cache" go run -race . -iters 5
```

Seed 0 (default) draws a random base seed and prints it; rerun with
`-seed` to reproduce a failure's chaos schedule (goroutine interleaving
is NOT reproduced — that residual nondeterminism is the point).

## The executable specification (`checkSafety`)

- **S1 Election Safety** — at most one leader per term (from the stream
  of "node N observed itself leader at term T" claims). Each scenario
  additionally carries an **exercise floor** (at least `minClaims`
  claims observed), reported as a distinct `EXERCISE FLOOR SHORTFALL`
  — it is a coverage assertion about the scenario, not a safety
  property of raft, and is never banner'd as a safety violation
  (audit-added; banner split per delta-review). Known
  masking-direction limitation: claims exist only for Readys the app
  loop consumed before `stopAll`, so a leadership acquired in the
  final window can go unrecorded — this can only hide a violation,
  never invent one.
- **S2 Log/Apply Agreement** — no two nodes apply different
  `(term, data)` at the same raft index (State Machine Safety observed
  at the apply boundary). This is also the double-commit detector:
  conflicting data at one index.
- **S3 Apply Monotonicity** — per node, applied indexes strictly
  increase and terms never decrease; additionally, re-delivered
  indexes and unmodeled entry types are recorded as **anomalies at
  apply time** and surfaced as violations (audit-added: the silent
  re-delivery guard previously made the index clause unfalsifiable).
- **S4 Completion** — every node applies every driven command; demanded
  only after the network heals (the conditioned-liveness shape: raft
  cannot promise progress under adversarial networks, only after them).
  Enforced primarily by the completion wait; the checker re-asserts it
  and — audit-added — **runs even when the wait times out**, so a
  liveness failure cannot mask a safety violation.

Client contract: proposals are retried until applied — at-least-once,
so duplicates are legitimate log entries that all nodes must still agree
on (S2 is what makes a true double-commit — same index, different
data — visible). S1–S3 are pure safety and hold at every instant; S4
is the completion witness that keeps the family non-vacuous (a cluster
that never commits anything cannot pass).

## Network model

Every message copy is delivered by its own goroutine: delivery order is
arbitrary **even in the "reliable" configuration**. Scenarios add, per
seeded RNG: drops (`DropProb`), duplication (`DupProb`, delivered as a
`proto.Clone` — raft mutates received proposals, so copies must not
share the object), bounded random delay (`MaxDelay`), and symmetric
group partitions. Messages to a crashed node are dropped.

## The family

| Scenario | Cluster | Chaos | What it exercises | Floor |
|---|---|---|---|---|
| `basic` | 3 | none (still reorders) | replication happy path | 1 |
| `reorder-dup` | 3 | 10% dup, ≤3ms delay | dedup/ordering, concurrent proposers | 1 |
| `chaos` | 5 | 15% drop, 5% dup, ≤3ms delay + a leader-isolation pulse | retry/catch-up machinery, forced re-election, heal-then-complete | 2 |
| `partition` | 5 | current leader partitioned into a 2-node minority | majority election + progress, deposed-leader proposals surviving heal; S1's main workout | 2 |
| `leader-churn` | 3 | forced transfer every 25ms, 40 cmds | election safety under churn, proposal forwarding | 2 |
| `crash-restart` | 3 | leader (odd seeds) or follower crash+restart | durability: nothing committed lost, and the RECOVERED node must win an election and commit | 2 |

(The chaos pulse and the leader-aware partition grouping are
audit-added: message-level chaos alone never times out a 2ms-heartbeat
leader, and a static partition only forces an election when the leader
happens to land in the minority — both left S1 checking a one-claim
stream.)

## Harness-construction findings (recorded for the machine twin)

1. **Raft mutates received proposal messages** (`node.go` propc path
   rewrites `From`): a network layer that duplicates messages must clone
   *before* first delivery, not lazily — found by `-race`.
2. **Forwarded proposals block inside `Node.Step` while leaderless**:
   stepping a `MsgProp` on the app loop wedges ticks (hence elections,
   hence the whole cluster) during leaderless windows. The harness steps
   proposals off-loop, bounded by a per-node context canceled at stop.
   Any future in-machine harness needs the same decoupling or a
   drop-and-retry client instead of forwarding.
3. **Restart requires persisting the ConfState, not just entries**
   (audit find): `RestartNode` restores membership from
   `Storage.InitialState()` — the snapshot metadata — and with
   `Config.Applied` set, the bootstrap conf-change entries are never
   re-delivered. A node restarted without a persisted ConfState has no
   voters, is silently unpromotable, and can never campaign; the
   harness persists it via `CreateSnapshot(appliedIndex, confState,
   nil)` before restart, and `crash-restart` now asserts the recovered
   node regains leadership WITH the full voter set and commits. The
   machine twin's storage model owes the same invariant.

Known coverage gap (delta-review observation, future family member):
the crash-restart victim is stopped at a quiescent point, so
`applied == commit` at restart and `Config.Applied` has nothing to
re-slice — the committed-but-unapplied crash state its anomaly guard
polices is never produced. A "crash mid-drive" scenario would make
that guard live.
