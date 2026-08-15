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
golean frontend or machine; the machine-runnable harness twin is a later
slice of the push.

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
  of "node N observed itself leader at term T" claims).
- **S2 Log/Apply Agreement** — no two nodes apply different
  `(term, data)` at the same raft index (State Machine Safety observed
  at the apply boundary).
- **S3 Apply Monotonicity** — per node, applied indexes strictly
  increase and terms never decrease.
- **S4 Completion** — every node applies every driven command; demanded
  only after the network heals (the conditioned-liveness shape: raft
  cannot promise progress under adversarial networks, only after them).

Client contract: proposals are retried until applied — at-least-once,
so duplicates are legitimate log entries that all nodes must still agree
on. S1–S3 are pure safety and hold at every instant; S4 is the
completion witness that keeps the family non-vacuous (a cluster that
never commits anything cannot pass).

## Network model

Every message copy is delivered by its own goroutine: delivery order is
arbitrary **even in the "reliable" configuration**. Scenarios add, per
seeded RNG: drops (`DropProb`), duplication (`DupProb`, delivered as a
`proto.Clone` — raft mutates received proposals, so copies must not
share the object), bounded random delay (`MaxDelay`), and symmetric
group partitions. Messages to a crashed node are dropped.

## The family

| Scenario | Cluster | Chaos | What it exercises |
|---|---|---|---|
| `basic` | 3 | none (still reorders) | replication happy path |
| `reorder-dup` | 3 | 10% dup, ≤3ms delay | dedup/ordering, concurrent proposers |
| `chaos` | 5 | 15% drop, 5% dup, ≤3ms delay | retry/catch-up machinery, heal-then-complete |
| `partition` | 5 | 2\|3 partition mid-run | majority progress, minority proposals surviving heal; S1's main workout |
| `leader-churn` | 3 | forced transfer every 100ms | election safety under churn, proposal forwarding |
| `crash-restart` | 3 | leader or follower crash+restart | durability: nothing committed is lost across a crash |

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
