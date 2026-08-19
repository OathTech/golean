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
apply(rd); rn.Advance(rd) }`. Bundling it is a deliberate ATOMICITY choice and
it is the design's most consequential one, so it is argued rather than assumed:

- etcd's own contract is that `Ready` must be processed and `Advance`d before
  the next one is taken; a driver that interleaves other nodes' steps INSIDE
  one node's ready-cycle is not modelling a faster network, it is modelling an
  application that violates the contract.
- The nondeterminism that matters — which message arrives when, which node
  times out first — lives in the EVENT ORDER, which is fully free. Splitting
  the harvest would add interleavings that no conforming application exhibits
  and that raft does not defend against.
- The go-run family already runs the harvest as one loop iteration per node
  (`harness.go`, `case rd := <-n.rn.Ready():`), so the twin's atomicity matches
  the executable spec's, which is what makes them twins.

Recorded as a design decision with an obligation attached: **when the goroutine
tier arrives, this bundling stops being a modelling choice and becomes a
property of the harness code**, and the granularity question moves to the
registry-boundary discussion (C-C), not here.

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
   (`rawnode.go:89`) that RETURNS an error (`ErrProposalDropped` when there is
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
| S4 completion — every node applied every command | a TERMINATION condition, not a per-step invariant: the driver stops when it holds, and the run is a completion WITNESS |

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

## §5 The H-2 seam decision — RECOMMENDED, with the measurement behind it

**The question** (raft-w2 log §4 D-5, handoff H-2): the no-op `Logger` overlay
makes `Fatal`/`Panic` do nothing, which SILENCES raft's own assertions —
`assertConfStatesEquivalent` (`util.go:320`, called from `raft.go:479` and
`:1936`) routes a failed ConfState-equivalence check through `Logger.Panic`.
W2.1's candidate answer was "`Panic`/`Panicf` panic with a fixed string, the
rest stay empty".

**The recommendation: neither. Keep upstream's `logger.go` VERBATIM and let the
HARNESS supply the Logger implementation.** H-3 makes this possible and the
measurement is in the log:

- With upstream `logger.go` in the tree, the export is clean and all ten
  `DefaultLogger` formatting methods land as fail-closed stubs. They are
  reachable ONLY through the `Logger` interface, and raft reaches for the
  package default at exactly one place — `Config.validate`, `raft.go:332`:
  `if c.Logger == nil { c.Logger = getLogger() }`. So a harness that SETS
  `Config.Logger` (the go-run family already does) never makes `DefaultLogger`
  the dynamic target, and a harness that forgets gets a loud fail-closed stop
  the first time raft logs — which is the right failure for a forgotten seam.
- The subject delta collapses from D-5's 144 changed lines to **two**: the two
  package-level initializers `defaultLogger`/`discardLogger`, which call
  `log.New(os.Stderr, …)` and are export-blocking under G-3 (a package-level
  variable has no per-declaration quarantine). Land H-11 and the delta is
  **zero** — the whole file becomes verbatim.
- The assertion question answers itself: the harness's `Logger.Panic` /
  `Panicf` genuinely `panic(...)`, so `assertConfStatesEquivalent` keeps its
  teeth, and the panic value is ours to choose (harness code carries no
  verbatim-ness claim, so it can be a fixed string with no fidelity debt). The
  six informational levels are empty bodies. `Fatal` panics too: under the twin
  there is no `os.Exit` to model and "stop the machine" is the honest reading
  of a fatal.

**Why this beats the ruled fixed-string seam.** The fixed-string seam puts the
teeth in the SUBJECT (a delta on upstream text, growing the ledger, re-derived
every time the pin moves); this puts them in the HARNESS, where the twin's
other decisions already live and where nothing is claimed to be etcd's code.
It also makes the subject's logger file a non-question forever, rather than a
recurring one at every rev bump.

**The residue, stated.** Two things do NOT change: (i) the argument-evaluation
finding — `stepLeader` calls `DescribeConfChange(cc)` as an argument to
`Infof`, so that rendering path runs whatever the logger does (log §2.3), and
(ii) `fmt`'s recovery of a Stringer panic (W2.1 §3's bound) still applies to
any harness logger that formats. A harness logger that formats NOTHING — empty
bodies plus a panic — has neither problem, which is another reason to prefer
it.

**The election-jitter seam (G-1 / H-15), same shape, same recommendation.** The
draw is one method body (`(*lockedRand).Intn`, `raft.go:96`) feeding one line
(`raft.go:2054`). Upstream itself treats the value as injectable — its
datadriven test env has a `set-randomized-election-timeout` command — which is
the fidelity argument that the jitter is a free parameter of the algorithm and
not semantics. So: seam `Intn` to draw from the harness's choice stream, record
it as a subject delta, and file the latitude entry against the RANGE
(`[electionTimeout, 2*electionTimeout)`), which is what the algorithm's
liveness argument actually depends on. Modelling `crypto/rand.Int` +
`math/big` as machine nondeterminism (the doctrinal alternative) buys nothing
the range does not already give and costs a big-integer model.

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
Under the recommended §5 seam the twin never calls `SetLogger` after setup, so
the registry is read-only during the run — which is exactly the kind of fact
the footprint check should CONFIRM rather than the design ASSERT.

**Where the theorem goes.** The disjointness result is the bridge from the
sequential twin to the goroutine twin (W5). Stating it now, with the
mechanization named, is what stops the sequential twin from being a dead end.

---

## §7 The datadriven-trace differential (W4's oracle) — feasibility, measured

`deps/raft/testdata/` holds **28 traces, 6,724 lines**. Command census across all of them, counted by
line-initial token (so a few may be output text rather than commands):
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

**The finding that decides the plan: the expected output is RENDERED TEXT.**
Every block's expectation is log lines (`INFO 1 became follower at term 0`) and
`DescribeReady` dumps. Reproducing those byte-for-byte needs the whole
rendering stack — `fmt` with `%x`/`%+v`, every `String()`, every `Describe*` —
which is precisely the machinery the sweep found dead-and-unlowerable. So:

- **Do NOT plan to replay upstream's expected outputs.** That path makes the
  fmt subset (§7 option 1 of the W2 log) a PREREQUISITE for the stage-4
  differential, inverting the dependency the roadmap wants.
- **Use the traces as COMMAND SEQUENCES and take the oracle from `go run`.**
  The differential is: our driver + one trace's commands, executed under
  `go run` and under the machine, comparing a canonical STATE PROJECTION
  (per node: term, vote, commit, applied, leader, state, the committed log's
  `(term,index,data)` triple list, the config's voter sets, and the sorted
  outgoing-message summaries). This is the "single-file driver on both sides"
  the master plan §W4 already specifies; the sweep is why it is the only
  reading that works.
- Upstream's expected-output blocks remain useful as a THIRD check, later,
  wherever rendering exists — a bonus tier, never a gate.

**Coverage estimate.** The command vocabulary the twin needs for the bulk of
the suite is `add-nodes`, `campaign`, `propose`, `deliver-msgs`,
`process-ready`, `stabilize`, `tick-heartbeat`/`tick-election`, plus the
read-only inspectors (`raft-state`, `raft-log`, `status`) which become
projections rather than commands. That is 8 command handlers, 3 projections and
a no-op `log-level` — **456 of the 506 non-`log-level` command instances,
~90%**. `process-append-thread`/`process-apply-thread` (16 instances) belong
to async storage writes and can be deferred with the traces that use them named.
`stabilize` is not a primitive: it is "run to quiescence", which in the twin is
a driver loop over the enabled set — and it is worth noting that stabilize's
determinism is exactly what the twin's choice stream generalizes.

---

## §8 The W4 execution plan (ordered slices, with scope estimates)

Each slice is validated before the next starts; each names what makes it done.

**W4.0 — unblock the export (3 gaps, all frontend-side).** H-9 (the inittask
double-escape), H-10 (`errors.New`), H-11 (per-declaration quarantine for
package-level vars). Done when `frontier-plan-postmerge.tsv` reduces to its
terminal row alone with no probe deltas. *Scope: small each; H-11 carries a
design question (what a quarantined global's read does) and should be ruled
before it is written.* Not this lane's to do.

**W4.1 — unblock the run (5 gaps).** H-12 (promoted `sync.Mutex` — 8 live
`MemoryStorage` methods), H-13 (`bytes.Equal` — 1 live), H-14 (`binary.LittleEndian`
— 2 live), H-6's ruling + implementation (`fmt` — 9 live), H-1's codec
(`proto.Clone`/`Size`/`Unmarshal` — all live). Done when
`reachability.py` reports ZERO live quarantined declarations over the tracked
tree. *Scope: H-1's codec dominates — it is the only one needing a fidelity
argument and a differential battery of its own (the `difftest.py` pattern
extends to it directly). H-12 is a semantics question, not a shim.*

**W4.2 — the twin, single node.** The driver, the event vocabulary, the harvest,
the projection function; n=1, no network. Runs under `go run` and the machine;
the projections agree. *Scope: one arc. This is where the twin's Go gets
written and where the corpus gains its first raft-shaped case.*

**W4.3 — the twin, n=3, reliable-first.** The network multiset, `deliver`,
`tick`, `propose`, the per-step invariant, the exercise floor. Done when a
recorded stream elects a leader, commits every command on every node, and S1–S4
hold at every step under both oracles. *Scope: one arc; this is M1 and most of
M3's mechanism.*

**W4.4 — the trace differential.** The 9-handler driver of §7, the state
projection, the 28 traces replayed under both oracles. Done when the suite is
green and recorded, with any skipped trace named and reasoned. *Scope: one to
two arcs; the variance is the handler set, not the traces.*

**W4.5 — the envelope.** The jitter seam's latitude entry, the network draws'
latitude entries, the perturbed-stream battery, the footprint check of §6.
Done when C-B's checklist item has its artifacts. *Scope: one arc, plus the
re-envelope arc's own schedule (W3.2), which it does not depend on but does
interact with.*

**Ordering note.** W4.2 can start against a scratch frontend carrying W4.0's
three fixes before they land, but must not be DECLARED green until they do —
the twin's value is that it runs on the real pipeline. W4.4 depends on W4.3's
driver, not the other way round: the traces are a breadth instrument over a
mechanism that already works, not the way to get the mechanism working.
