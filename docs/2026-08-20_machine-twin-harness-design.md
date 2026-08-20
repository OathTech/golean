# The machine-twin harness — design (2026-08-20)

Status: DESIGN, not built. Written by raft lane W2.2 (`docs/raft-w3-log.md`)
against the sweep in that log, which is the evidence for every "this is
reachable / this is dead" claim here. Charter: master plan
(`docs/2026-08-15_raft-master-plan.md`) §W2.2 — "the machine-twin harness
design: RawNode-driven node loops (no node.go / context / time), logical tick
schedule from the choice stream, in-machine channel network, the executable
Agreement checker as harness Go".

Companions to read first: `raftharness/README.md` + `harness.go` (the go-run
family — the executable specification this twin must not rewrite),
`docs/2026-08-15_raft-push-p0-scoping.md` §3/§7,
`docs/2026-08-04_nondeterminism-doctrine.md` (choice-site discipline),
`docs/2026-08-14_harness-style-scoping.md` §8 (capstone form).

## Rulings and corrections, 2026-08-20

**USER RULINGS** (also recorded in `docs/raft-w3-log.md` §5; not this lane's to
re-open):

- **Q2 — the H-2 logger seam: the revised recommendation is ADOPTED.** Upstream
  `logger.go` stays VERBATIM and the HARNESS supplies the `Logger`. **Amended**
  by the audit: the harness supplies BOTH `Config.Logger` AND
  `raft.SetLogger(...)`, with the same stateless logger value — `getLogger()`
  has six call sites, not one, and three live ones are in `MemoryStorage`, which
  never consults `Config.Logger`. §5.
- **Q3 — the fmt story: OPTION 1.** A modeled `Sprintf` SUBSET over the measured
  verb/kind set, differential-pinned per verb. The census it ranges over is log
  §2.4, corrected: `Sprintf` ×6, `Errorf` ×11, `Fprintf` ×3, verbs
  `%d %s %v %+v %x %q` (`%v` and `%q` arrive with `DescribeConfChange`'s three
  `Fprintf` sites, which the first liveness census could not see). §8's W4.1.

**CORRECTIONS this round made to the design's own claims**, each argued in
place: the Ready-harvest atomicity is a deliberate ENVELOPE NARROWING with a
re-envelope obligation, NOT a consequence of etcd's contract (§2, refuted by
`rawnode.go:411`, `node.go`'s select, `doc.go:101-103`); the logger seam is two
places, not one (§5); the election-jitter draw is a LIVE RUN BLOCKER, not a
deferred design question (§5); §7's "every block's expectation is rendered text"
is false for 249 of 558 blocks (§7); W4.1's done criterion was fail-open (§8).

---

## §1 What the twin is, in one paragraph

A single Go program, canonical Go, that runs under BOTH `go run` and the
machine: **n RawNodes, no goroutine per node, no clock, no context**. A driver
loop consumes an EVENT from the choice stream, applies it to one node
atomically (`Step` / `Tick` / `Propose`, then a full Ready harvest), folds the
harvested messages into a network multiset, and checks the safety invariant.
The go-run family (`raftharness/`) stays exactly as it is: it is the
concurrent, wall-clock, chaos-network EXECUTABLE SPEC, and its role in the
push is to be the thing the twin is a twin OF — same properties, different
mechanism. This document says how the twin realizes those properties without
goroutines, time, or context, and what the machine owes at each seam.

**Why not goroutines.** The concurrent shape is P2/W5's, and it is a strictly
larger claim resting on the re-envelope arc (W3.2) and the granularity ruling
(C-C). A sequential driver whose EVENT ORDER is drawn from the choice stream
gets the interleaving envelope that matters for raft's safety properties — raft
is a message-passing algorithm; its adversary is the network and the timer, not
the Go scheduler — at a fraction of the machinery. The goroutine twin is a
later tier over the same subject and the same checker, not a different program.
This is the same split the scoping doc's §3.5 asks for in the statement's
documentation, made structural.

---

## §2 The event vocabulary

One step of the driver consumes one event. The vocabulary is deliberately
small, and every member is a raft-level action with an argument the choice
stream picks:

| event | argument(s) | effect |
|---|---|---|
| `deliver(i, m)` | node `i`, an index `m` into the network multiset | `rn[i].Step(msg)`, then HARVEST (below) |
| `tick(i)` | node `i` | `rn[i].Tick()`, then HARVEST |
| `propose(i, v)` | node `i`, a value `v` from the pending command list | `rn[i].Propose(v)`, then HARVEST |
| `drop(m)` | an index into the multiset | remove without delivering |
| `dup(m)` | an index into the multiset | insert a CLONE beside it |

`campaign`, `transfer`, `forget-leader`, `conf-change` are TIER-2 members of
the same shape; the first three are what a first twin needs.

**The harvest is part of the event, not a separate one.** After the RawNode
call: `if rn.HasReady() { rd := rn.Ready(); persist(rd); record(rd); send(rd);
apply(rd); rn.Advance(rd) }`.

**This is a DELIBERATE ENVELOPE NARROWING, not a fact derived from etcd's
contract** (rewritten 2026-08-20; the first draft claimed the contract forbids
interleaving, and the audit refuted it):

- `rawnode.go:411` keeps per-RawNode `stepsOnAdvance`, i.e. upstream's own code
  is built to accept steps that arrive DURING a ready-cycle and replay them at
  `Advance`. A driver that interleaves is not violating anything; upstream has a
  mechanism for exactly that case.
- upstream's `node.go` loop is single-threaded but keeps `recvc`, `propc` and
  `tickc` ARMED while `advancec` is pending — so real etcd applications do step
  a node between `Ready()` and `Advance()`, routinely.
- `doc.go:101-103` says an application may call `Advance` "at any time after
  step 1", which is a licence to interleave, not a prohibition.

So the honest statement is: **the v1 twin models FEWER interleavings than
upstream licenses.** The bundling is ours, chosen because S1–S4 are the first
thing to prove and a narrower interleaving space makes the first proofs
tractable; it is not a claim about what conforming applications do.

**Recorded with a re-envelope obligation** (the W3.2 register pattern — a
narrowing is scaffolding carrying a debt, never a fidelity achievement):

| | |
|---|---|
| **what is excluded** | every schedule in which node `i` is stepped, ticked or proposed to between its own `Ready()` and its `Advance(rd)` — including the `stepsOnAdvance` replay path, and including another node's harvest running inside `i`'s |
| **why v1 accepts it** | the S1–S4 proofs come first, and they are about the message-passing algorithm, whose adversary is the network and the timer; the excluded schedules add no new message orders, only new points at which a node's local state is observed mid-cycle |
| **what it costs** | a theorem about the twin is, at v1, a theorem about a SUBSET of conforming drivers. Any statement must say so (scoping §3.5) |
| **how it widens** | additively, and without touching the checker: split `harvest` into its own event kind with the node index as its argument, and the excluded schedules become reachable. The event vocabulary is already indexed by node, so this is a new row in §2's table, not a redesign |
| **when** | W4.5, beside the other envelope work, and before any claim that the twin covers upstream's driver contract |

The go-run family (`harness.go`, `case rd := <-n.rn.Ready():`) happens to run
the harvest as one loop iteration per node, so the twin and the executable spec
are narrowed the SAME way — which is what keeps them twins, and is also why
neither of them witnesses the excluded schedules. When the goroutine tier
arrives the bundling stops being a modelling choice and becomes a property of
the harness code, and the granularity question moves to the registry-boundary
discussion (C-C).

### The choice-site spec (what `∀ch` quantifies)

Exactly four draws, each with its range stated as the envelope argument the
latitude inventory will need (C-B):

1. **Which event kind**, over the ENABLED set at that state: any node may tick;
   any in-flight message may be delivered/dropped/duped; any node may be
   proposed to while commands remain. Range: the enabled set, unrestricted —
   this is the whole interleaving freedom.
2. **Which node**, uniform over `1..n`.
3. **Which message**, uniform over the multiset's live indices. Delivery order
   is therefore ARBITRARY, including reordering between the same pair — which
   is what the go-run family gets from "one goroutine per message copy" and
   what a FIFO queue would silently forbid.
4. **The election-timeout jitter** — see §5. Range:
   `[electionTimeout, 2*electionTimeout)`, raft's own contract.

**The reliable-first envelope, exactly.** v1 sets `drop` and `dup` OFF: the
network never loses or duplicates, but it reorders and delays without bound
(a message may sit in the multiset for any number of events, including
forever-until-the-run-ends). This is a strictly weaker theorem than raft's
design point and the statement's docstring must say so (scoping §3.5). The
mechanism does not change when chaos is turned on — `drop`/`dup` are already
in the vocabulary, gated by a flag that the choice stream can own instead. That
is the point of writing them now: the tier-2 envelope is a flag, not a rewrite.

**Fairness is not assumed and must not be precluded.** The driver never
"eventually delivers" anything; an adversarial stream may starve a node
forever. That is the FLP tension the scoping doc's §3.1 records, and it is why
the theorem shape is conditioned safety + a completion witness rather than
total correctness. The choice-consumption points above keep every scheduling
pick identifiable and the enabled set recoverable, which is the 2026-08-14
fairness non-preclusion requirement applied to this harness.

---

## §3 The network as a multiset, and the two go-run findings it must honour

The network is a slice of `*pb.Message` plus a liveness bitmap (removal by
index, never by shifting — indices are what the choice stream names). No
channels, no goroutines, no delay counters: "delay" is just "not chosen yet".

Two findings from `raftharness/README.md` §"Harness-construction findings" are
DESIGN INPUTS here, not trivia:

1. **Raft mutates delivered proposal messages.** `dup` must CLONE at insertion,
   before either copy is delivered. In the twin this is `proto.Clone` — which
   is H-1/G-4, i.e. the twin's `dup` cannot exist until the codec does. v1 has
   `dup` off, so this is a tier-2 dependency, recorded so it is not discovered
   late.
2. **Forwarded proposals block inside `Node.Step` while leaderless.** This is a
   `node.go` problem — the propc channel — and the twin does not have it, by
   construction: `node.go` is not in the subject tree (only its declaration
   subset is), and `RawNode.Propose` is a direct `rn.raft.Step(MsgProp)`
   (`rawnode.go:91`, in `Propose` at `rawnode.go:90`) that RETURNS an error
   (`ErrProposalDropped` when there is
   no leader to accept it). The
   twin's client is therefore DROP-AND-RETRY: a `propose` event whose error is
   non-nil leaves the command in the pending list. That is the "drop-and-retry
   client instead of forwarding" the master plan §W2.2 already directs, and the
   RawNode layer gives it for free.

A third finding is load-bearing for storage: **restart requires persisting the
ConfState**, not just entries. The twin's storage model owes the same invariant
if it ever grows a crash-restart event; v1 has none, and the invariant is
recorded here so it lands with the event rather than after it.

---

## §4 The executable invariant, per step

`raftharness/`'s `checkSafety` is the specification and this design does not
rewrite it — it RESHAPES it from "fold at termination" to "check at every
step", which is what makes the twin's failure witness a prefix rather than a
whole run.

| go-run | twin |
|---|---|
| S1 election safety — at most one leader per term, from claims recorded when a Ready carries `SoftState.RaftState == StateLeader` | identical, but the claim is recorded inside the harvest, so the check runs on every event: `leaderOf[term]` map, violation on disagreement |
| S2 log/apply agreement — no two nodes apply different `(term, data)` at one index | identical: an `appliedAt[index] = (term, data)` map, checked at apply time |
| S3 apply monotonicity + the anomaly channel | identical, per node, at apply time |
| S4 completion — every node applied every command | a TERMINATION condition, **not** a per-step invariant: the driver stops when it holds, and the run is a completion WITNESS |

**S1–S3 are the invariant; S4 is the stopping condition.** Stated because §8's
slice criteria used to say "S1–S4 hold at every step", which is not a thing S4
can do — S4 is false at every step of a run until the last one, by construction.
The W4.3 criterion below says the checkable thing instead.

**The per-step form is the important change.** A verdict folded at the end can
only say "this run was safe"; a per-step invariant is a state predicate, which
is what a Lean statement over the interpreter can quantify over
(`run = .ok r → Agreement r`, the §0 end state). The checker stays HARNESS GO —
first-order, readable from base definitions, no Iris — per the statement-TCB
doctrine.

**The exercise floor comes too.** The go-run family reports an
`EXERCISE FLOOR SHORTFALL` separately from a safety violation because a cluster
that never elects anyone satisfies S1 vacuously. The twin needs it MORE, not
less: its completion witness is a single recorded stream, and a stream that
achieves nothing would be a forgery-by-deadlock exactly as the scoping doc
warns. Floor: at least one leader claim and at least one committed command.

---

## §5 The H-2 seam decision — RULED, with the measurement behind it

**Status: RULED by the user 2026-08-20 (Q2) — the revised recommendation below
is ADOPTED, with the `SetLogger` amendment the audit forced.** Recorded also in
`docs/raft-w3-log.md` §5.

**The question** (raft-w2 log §4 D-5, handoff H-2): the no-op `Logger` overlay
makes `Fatal`/`Panic` do nothing, which SILENCES raft's own assertions —
`assertConfStatesEquivalent` (`util.go:320`, called from `raft.go:479` and
`:1936`) routes a failed ConfState-equivalence check through `Logger.Panic`.
W2.1's candidate answer was "`Panic`/`Panicf` panic with a fixed string, the
rest stay empty".

**The ruling: neither. Keep upstream's `logger.go` VERBATIM and let the
HARNESS supply the Logger implementation.** H-3 makes this possible and the
measurement is in the log:

- With upstream `logger.go` in the tree the export is clean, and **eleven**
  declarations land as fail-closed stubs: the ten `DefaultLogger` formatting
  methods (`Debug`/`Debugf`/`Info`/`Infof`/`Error`/`Errorf`/`Warning`/
  `Warningf`/`Fatal`/`Fatalf`) **and the package-level `header` helper**
  (`logger.go:140`, `fmt.Sprintf`), which the first draft missed. `Panic` and
  `Panicf` are NOT among them — they delegate to the embedded `*log.Logger`, so
  they lower and fail closed at the imported stub when called, which is the same
  outcome by a different route.
- The subject delta is **three lines**, not two: the two package-level
  initializers `defaultLogger`/`discardLogger` (which call `log.New(os.Stderr, …)`
  and are export-blocking under G-3), plus the `"io"` import they orphan.
  Measured, not estimated — the walk was run with upstream's file in the tree.
  Land H-11 and the delta is **zero** — the whole file becomes verbatim.
- The assertion question answers itself: the harness's `Logger.Panic` /
  `Panicf` genuinely `panic(...)`, so `assertConfStatesEquivalent` keeps its
  teeth, and the panic value is ours to choose (harness code carries no
  verbatim-ness claim, so it can be a fixed string with no fidelity debt). The
  harness logger implements the `Logger` interface's twelve methods as
  **eight empty bodies** (`Debug`/`Debugf`/`Info`/`Infof`/`Error`/`Errorf`/
  `Warning`/`Warningf` — four informational levels, each with a formatted
  variant) and **four that panic**. `Fatal` panics too: under the twin
  there is no `os.Exit` to model and "stop the machine" is the honest reading
  of a fatal.

### The amendment: `Config.Logger` alone is NOT the seam

The recommendation as first written said raft reaches for the package default
"at exactly one place — `Config.validate`". **That is false, and the difference
matters.** `getLogger()` has SIX call sites, and only one of them is
`Config.validate`:

| site | declaration | live under the twin? |
|---|---|---|
| `raft.go:333` | `Config.validate` — `if c.Logger == nil { c.Logger = getLogger() }` | LIVE |
| `storage.go:154` | `MemoryStorage.Entries` | **LIVE** |
| `storage.go:252` | `MemoryStorage.CreateSnapshot` | **LIVE** |
| `storage.go:322` | `MemoryStorage.Append` | **LIVE** |
| `storage.go:276` | `MemoryStorage.Compact` | dead (the twin never compacts) |
| `status.go:102` | `Status.String` | dead |

The four `MemoryStorage` sites are `getLogger().Panicf(...)` on bound-violation
paths, and they consult the package-level REGISTRY — `Config.Logger` is not in
scope there and setting it does nothing for them. Three are live.

**So the harness supplies BOTH.** At setup, before any node is constructed:

```go
lg := &harnessLogger{}     // stateless: no fields, no writes
raft.SetLogger(lg)         // the package registry — covers the 6 getLogger() sites
cfg.Logger = lg            // the per-node seam — covers every r.logger.* call
```

**Sharing one logger value across all n nodes is shared-nothing-safe, and this
is a side condition of the reduction theorem (§6), not a stylistic note.** It
holds because `harnessLogger` is STATELESS: no fields, so every method writes
nothing and reads nothing, so its footprint is empty and it cannot appear in any
pairwise-disjointness obligation. A logger that buffered output — the obvious
"let me see what happened" temptation — would be shared MUTABLE state touched by
every node on every event, and would silently invalidate §6's whole argument. If
the twin ever needs a recording logger it must be PER NODE, and §6's footprint
check must be re-run.

The registry is written once, before the run, and never again, so
`raftLoggerMu`/`raftLogger` are read-only during the run — which §6 lists as a
fact the footprint check should CONFIRM rather than the design assert.

**Why this beats the ruled fixed-string seam.** The fixed-string seam puts the
teeth in the SUBJECT (a delta on upstream text, growing the ledger, re-derived
every time the pin moves); this puts them in the HARNESS, where the twin's
other decisions already live and where nothing is claimed to be etcd's code.
It also makes the subject's logger file a non-question forever, rather than a
recurring one at every rev bump.

**The residue, stated.** Two things do NOT change: (i) the argument-evaluation
finding — `stepLeader` calls `DescribeConfChange(cc)` as an argument to
`Infof` (`raft.go:1340`), so that rendering path runs whatever the logger does
(log §2.3), and it drags three `fmt.Fprintf`s and a live `strings.Builder`
(G-10) in with it; and (ii) `fmt`'s recovery of a Stringer panic (W2.1 §3's
bound) still applies to any harness logger that formats. A harness logger that
formats NOTHING — empty bodies plus a panic — has neither problem, which is
another reason to prefer it. Note that (i) is NOT fixed by the logger choice at
all: it is an argument, and Go evaluates it.

**The election-jitter seam (G-1 / H-15) — same shape, but it is a LIVE RUN
BLOCKER, not a design question with time on it.** The audit's correction (log
§2.5): the walk's own probe delta replaced `(*lockedRand).Intn`'s body, so the
census never saw the draw's refusal and G-1 read as a pure export blocker. It
is not. `Intn` (`raft.go:97`) feeds `resetRandomizedElectionTimeout`
(`raft.go:2054`), which `becomeFollower` calls, which `(*raft).Step` reaches —
so the twin stops on it the first time a node becomes a follower, which is
immediately. Measured refusal:
`package-selector call rand.Int (package "crypto/rand" surface not modeled)`.

**The fix direction is the CHOICE SITE, and this is doctrine rather than
convenience.** Election jitter is nondeterminism; nondeterminism belongs to the
ENVELOPE, and the envelope is argued against the algorithm's own contract. So:
the draw becomes a choice-consumption point (§2's draw 4), the latitude entry is
filed against the RANGE `[electionTimeout, 2*electionTimeout)` — which is what
raft's liveness argument actually depends on — and `crypto/rand` + `math/big`
are never modeled. Modelling them would buy nothing the range does not already
give, cost a big-integer model, and (worse) turn a latitude point into a
deterministic pin. Upstream agrees the value is a free parameter: its datadriven
test env has a `set-randomized-election-timeout` command.

Scheduled in **W4.1**, with the other run-blockers.

---

## §6 The shared-nothing footprint check (the reduction theorem's side condition)

The sequential twin's whole claim to be about the CONCURRENT system is a
reduction: if the per-event actions touch disjoint state, the sequential
interleaving of events is a faithful stand-in for concurrent execution. That
side condition must be MECHANIZED, not asserted.

**The obligation.** For each event, the set of heap locations written by that
event must be disjoint from the locations read or written by every other node's
concurrent event, EXCEPT the network multiset, which is the one shared object
and is touched under a discipline (insert at harvest, remove at deliver).

**How the existing machinery discharges it.** The race machinery already
computes per-step read/write sets — it is what the data-race detection in the
concurrency semantics is built on (`docs/2026-08-09_sync-package-design.md` and
the NPDRF register). The check is then: instrument a twin run, collect the
footprint of each event, and assert pairwise disjointness of (node `i`'s
footprint) and (node `j`'s footprint) for `i ≠ j`, modulo the network object.
Two properties make this cheap here: RawNodes share NOTHING by construction —
the vendored root package's only MUTABLE package-level state is `globalRand`,
whose single method the §5 jitter seam replaces (leaving the variable inert),
and the logger registry, which the harness owns; everything else at package
scope is an error sentinel or an immutable lookup table, checked by reading
every `var` in the tree — and `MemoryStorage` is per node.

**The one shared object that is NOT the network:** `raftLoggerMu` /
`raftLogger`, the package-level logger registry (kept in W2.1's overlay
precisely because dropping the mutex would smuggle in a concurrency delta).
Under the ruled §5 seam the twin calls `SetLogger` ONCE, at setup, before any
node exists, and never again — so the registry is read-only during the run.
Which is exactly the kind of fact the footprint check should CONFIRM rather
than the design ASSERT.

**The checklist the footprint run must discharge**, each item a place where
"shared nothing" is a claim rather than an obvious truth:

1. **`raftLogger` is written once, pre-run.** Violated the moment anything calls
   `SetLogger` mid-run.
2. **The `Logger` VALUE is stateless.** §5's amendment shares one logger across
   all n nodes; that is only safe because `harnessLogger` has no fields. A
   logger with a buffer is shared mutable state on every node's every event.
3. **`emptyState` is an aliased pointer** (`node_decls.go:17`,
   `emptyState = &pb.HardState{}`), and `bootstrap.go:48` assigns it straight
   into a RawNode's `prevHardSt`. Two bootstrapped nodes would share one
   `*pb.HardState`. Dead under the v1 twin (`Bootstrap` is measured dead, log
   §2.3) and read-only through `IsEmptyHardState` — but it is a package-level
   pointer that reaches per-node state, which is precisely the shape this check
   exists to catch, so it is enumerated rather than waved off.
4. **Every other package-level `var` in the tree is an error sentinel or an
   immutable lookup table** — checked by reading all of them; `globalRand` is
   the exception and the §5 jitter choice site leaves it inert.
5. **`MemoryStorage` is per node**, and its embedded mutex is uncontended once
   the driver is sequential — which is a reason the G-6 fix must not quietly
   become "drop the lock".

**Where the theorem goes.** The disjointness result is the bridge from the
sequential twin to the goroutine twin (W5). Stating it now, with the
mechanization named, is what stops the sequential twin from being a dead end.

---

## §7 The datadriven-trace differential (W4's oracle) — feasibility, measured

`deps/raft/testdata/` holds **28 traces, 6,724 lines, 558 blocks**. Command
census across all of them, counted by the command line of each `----`-separated
block (re-counted 2026-08-20 — the first draft counted line-initial tokens and
hedged that "a few may be output text"; block-anchored counting removes the
hedge and reproduces the same numbers):
`stabilize` 136, `campaign` 54, `process-ready` 53, `propose` 50,
`deliver-msgs` 48, `add-nodes` 37, `raft-state` 30, `status` 18,
`propose-conf-change` 18, `raft-log` 15, `tick-heartbeat` 12,
`process-append-thread` 12, `forget-leader` 9, `process-apply-thread` 4,
`tick-election` 3, `set-randomized-election-timeout` 2, `compact` 2,
`transfer-leadership` 1, `send-snapshot` 1, `report-unreachable` 1.

**The format.** Each block is `command args` / `----` / expected output. The
driver is `deps/raft/rafttest/interaction_env*.go` (a `RawNode` per node plus a
message bag — i.e. structurally the twin already), with `cockroachdb/datadriven`
supplying the parse-and-compare loop.

**The finding that shapes the plan: most expectations are RENDERED TEXT — but
not all, and the first draft's "every block" was wrong.** Counted exactly
(a block is a `----` separator; 558 of them):

| expected output | blocks | share |
|---|---|---|
| literally `ok` | 249 | **44.6%** |
| rendered text — log lines (`INFO 1 became follower at term 0`), `DescribeReady` dumps, `raft-state` tables | 309 | 55.4% |

Reproducing the 309 byte-for-byte needs the whole rendering stack — `fmt` with
`%x`/`%+v`, every `String()`, every `Describe*` — which is precisely the
machinery the sweep found mostly dead-and-unlowerable. But the 249 need NO
rendering at all: their expectation is a constant. So:

- **Do NOT make replaying upstream's expected outputs the PLAN.** Requiring all
  558 would make the fmt subset a PREREQUISITE for the stage-4 differential,
  inverting the dependency the roadmap wants.
- **The 249 `ok` blocks are a free tier, and should be taken.** They are a real
  check — they assert the command was ACCEPTED, which catches a driver that
  silently no-ops — and they cost nothing beyond the driver W4.3 already builds.
  Fold them into W4.4 rather than deferring them with the rendering ones.
- **Use the traces as COMMAND SEQUENCES and take the oracle from `go run`.**
  The differential is: our driver + one trace's commands, executed under
  `go run` and under the machine, comparing a canonical STATE PROJECTION
  (per node: term, vote, commit, applied, leader, state, the committed log's
  `(term,index,data)` triple list, the config's voter sets, and the sorted
  outgoing-message summaries). This is the "single-file driver on both sides"
  the master plan §W4 already specifies; the sweep is why it is the only
  reading that works.
- The 309 RENDERING-bearing blocks remain useful as a THIRD check, later,
  wherever rendering exists — a bonus tier, never a gate.

**Coverage estimate.** The command vocabulary the twin needs for the bulk of
the suite is `add-nodes`, `campaign`, `propose`, `deliver-msgs`,
`process-ready`, `stabilize`, `tick-heartbeat`/`tick-election`, plus the
read-only inspectors (`raft-state`, `raft-log`, `status`) which become
projections rather than commands. That is 8 command handlers, 3 projections and
a no-op `log-level` — **456 of the 506 non-`log-level` blocks, 90.1%**.
`process-append-thread`/`process-apply-thread` (16 blocks) belong
to async storage writes and can be deferred with the traces that use them named.

**Read that 90% as blocks, not as traces.** Only **7 of the 28 traces (25%)**
are covered ENTIRELY by the 8+3 handler set (`campaign`, `checkquorum`,
`lagging_commit`, `prevote`, `probe_and_replicate`, `replicate_pause`,
`single_node`); the other 21 each contain at least one command outside it. So
"90% coverage" buys a broad SAMPLE of raft behaviour, and a small set of
end-to-end replayable traces. Both are worth having and they are not the same
claim — W4.4's done criterion should name the whole-trace set, since a partially
replayed trace has no meaningful pass/fail.
`stabilize` is not a primitive: it is "run to quiescence", which in the twin is
a driver loop over the enabled set — and it is worth noting that stabilize's
determinism is exactly what the twin's choice stream generalizes.

---

## §8 The W4 execution plan (ordered slices, with scope estimates)

Each slice is validated before the next starts; each names what makes it done.

**W4.0 — unblock the export (2 measured blockers, both frontend-side).** H-9
(the inittask double-escape) and H-10 (`errors.New`). H-11 (per-declaration
quarantine for package-level vars) is an ALTERNATIVE to H-10 for the nine
globals, not a third requirement — do one of the two, and prefer H-10, which is
shim-shaped and retires the in-body sites too. Done when `frontier-plan.tsv`
reduces to its terminal row alone with no probe deltas. *Scope: small each;
H-11, if taken, carries a design question (what a quarantined global's read
does) and should be ruled before it is written.* Not this lane's to do.

**W4.1 — unblock the run (8 causes over 26 live declarations; G-2's in-body
`errors.New` sites are the ninth and retire with W4.0's H-10).** H-12 (promoted
`sync.Mutex` — 8 live `MemoryStorage` methods), H-13 (`bytes.Equal` — 1 live),
H-14 (`binary.LittleEndian` — 2 live), H-6's implementation (`fmt`, ruled
OPTION 1 — a modeled `Sprintf` subset over the measured verb/kind set,
differential-pinned per verb; 20 calls in 10 live declarations, verbs
`%d %s %v %+v %x %q`),
H-17 (`strings.Join` — 1 live, and note it is INSIDE `newRaft`, so H-6 alone
does not unblock `NewRawNode`), H-18 (`strings.Builder`, a rider on H-6),
**H-15 (the election-jitter CHOICE SITE — 1 live, `(*lockedRand).Intn`; the
draw becomes a choice-consumption point with the range
`[electionTimeout, 2*electionTimeout)` filed as a latitude entry, never a
modeled `crypto/rand`)**, and H-1's codec (`proto.Clone`/`Size`/`Unmarshal` —
all three live).

*DONE CRITERION — restated, because the first version was FAIL-OPEN.* It used
to read "`reachability.py` reports ZERO live quarantined declarations", which
three classes of fail-closed stop slip straight past: the `proto.*` stand-ins
are explicit `panic`s, so they LOWER and were never quarantined; imported
stdlib declaration-only stubs (`strings.Builder.String`) are quarantined but
were filtered out of the query set as "not a raft gap"; and a probe delta that
replaces a body hides whatever that body would have refused (`Intn` — the
defect that cost this design its G-1 row). So:

> **W4.1 is done when `sweep.py` reports ZERO REACHABLE fail-closed stops of
> ANY class over the tracked tree, enumerated by class:**
> 1. zero live QUARANTINED subject declarations,
> 2. zero live quarantined IMPORTED stdlib stubs,
> 3. zero live subject declarations whose body is a fail-closed `panic` stand-in
>    (the `proto` package: `Clone`, `Marshal`, `Unmarshal`, `Size`),
> 4. zero live declarations MASKED by a probe delta — equivalently, the walk
>    plan has no body-replacing rows left, since W4.0 retires the only one,
> 5. and the RESIDUAL-SINK report is empty, so (1)–(4) range over the whole
>    reachable graph rather than over what the first-order walk could see.
>
> Classes (2)–(5) are exactly the ones a green run would not have shown you.

*Scope: H-1's codec dominates — it is the only one needing a fidelity argument
and a differential battery of its own (the `difftest.py` pattern extends to it
directly). H-12 is a semantics question, not a shim. H-15 is an envelope
question and its latitude entry is W4.5's, but the choice site itself must land
here or the twin cannot run.*

**W4.2 — the twin, single node.** The driver, the event vocabulary, the harvest,
the projection function; n=1, no network. Runs under `go run` and the machine;
the projections agree. *Scope: one arc. This is where the twin's Go gets
written and where the corpus gains its first raft-shaped case.*

**W4.3 — the twin, n=3, reliable-first.** The network multiset, `deliver`,
`tick`, `propose`, the per-step invariant, the exercise floor. Done when a
recorded stream elects a leader, commits every command on every node, **S1–S3
hold at EVERY step and S4 holds at the last** (S4 is the stopping condition, not
an invariant — §4), under both oracles, with the exercise floor met so the
verdict is not vacuous. *Scope: one arc; this is M1 and most of
M3's mechanism.*

**W4.4 — the trace differential.** The 9-handler driver of §7, the state
projection, the traces replayed under both oracles. Done when (a) the **7
whole-trace-covered files** replay green end to end, (b) the **249 `ok`-expecting
blocks** are asserted directly (they need no rendering — §7), and (c) every
partially-covered trace is named with the command that stops it. A partially
replayed trace has no meaningful pass/fail, so it is reported, not counted. *Scope: one to
two arcs; the variance is the handler set, not the traces.*

**W4.5 — the envelope.** The jitter draw's latitude entry (range
`[electionTimeout, 2*electionTimeout)`), the network draws' latitude entries,
the perturbed-stream battery, the footprint check of §6 against its five-item
checklist, and **the harvest-atomicity re-envelope obligation of §2** — the one
narrowing this design takes knowingly. Done when C-B's checklist item has its
artifacts and the §2 obligation is either discharged (the `harvest` event exists
and the excluded schedules are reachable) or re-recorded with a date. *Scope: one arc, plus the
re-envelope arc's own schedule (W3.2), which it does not depend on but does
interact with.*

**Ordering note.** W4.2 can start against a scratch frontend carrying W4.0's
two fixes before they land, but must not be DECLARED green until they do —
the twin's value is that it runs on the real pipeline. W4.4 depends on W4.3's
driver, not the other way round: the traces are a breadth instrument over a
mechanism that already works, not the way to get the mechanism working.
