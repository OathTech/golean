// THE MACHINE-TWIN HARNESS, v1 (W4.2/W4.3 — the harness design's §1-§4
// realized; docs/raft-w42-log.md item 2).
//
// A single Go program, canonical Go, run under BOTH `go run` and the
// machine by tools/raftsubject/runprobe.py: n RawNodes, no goroutine per
// node, no clock, no context. A driver loop applies EVENTS to one node
// atomically and checks the safety invariant per step. THE SCHEDULE IS
// THE INPUT: v1 drives named, hand-written schedules (the tables at the
// bottom) rather than the choice stream — same trace on both oracles for
// the same schedule is the claim runprobe.py checks. The ∀ch-quantified
// form (events drawn from the machine's choice stream) is the membership
// lane's, over this same mechanism.
//
// The event vocabulary (design §2): tick(i), campaign(i), propose(i),
// deliver(i,k) — plus the drain/drainRev macros (deliver-to-quiescence in
// insertion / reverse-insertion order), which play the ROLE upstream's
// `stabilize` plays and are what the perturbation schedules vary. They
// are not the same procedure, and the gloss that said they were is
// corrected here (pre-merge audit, 2026-08-21): upstream `stabilize`
// alternates "harvest EVERY listed node that HasReady" with "deliver
// every listed node's bag", to a fixed point; `drain` delivers one
// message at a time and harvests only the RECIPIENT (deliverIdx). A node
// holding a Ready but receiving nothing is harvested by `stabilize` and
// not by `drain`. Same quiescence target, different interleaving — which
// is the point of an event vocabulary whose grain is one node per step
// (design §2). drop/dup are
// OFF in v1 (the reliable-first envelope: the network reorders and
// delays without bound — a message may sit in the multiset forever — but
// never loses or duplicates; a strictly weaker theorem than raft's
// design point, stated where the statement will live). `campaign` is
// TIER-2 in the design's table but is IN v1, for a measured reason:
// timeout-driven elections consume the D-11 jitter draw, whose VALUE
// differs across oracles (that is the point of a choice site), so a
// jitter-sensitive schedule cannot promise same-trace-on-both-oracles.
// v1 schedules keep per-node unreset election ticks < ElectionTick and
// drive elections explicitly — exactly what upstream's own datadriven
// traces do with their `campaign` command. The jitter ENVELOPE is the
// membership lane's (maps/jitter-draw pins it; the latitude entry is
// W4.5's).
//
// THE HARVEST IS PART OF THE EVENT (design §2): after the RawNode call,
// loop `for HasReady { persist; record; send; apply; Advance }` to LOCAL
// quiescence. This is the RECORDED ENVELOPE NARROWING of design §2 — the
// v1 twin models FEWER interleavings than upstream licenses (upstream's
// stepsOnAdvance machinery, node.go's armed channels, and doc.go's
// "Advance at any time" all license stepping a node between Ready and
// Advance). The narrowing carries a re-envelope obligation (W4.5: a
// `harvest` event kind of its own makes the excluded schedules
// reachable, additively). Note the loop-to-quiescence form is the same
// bundling W4.1's THE-MOMENT probe used, which is what makes
// probeTwinSingle reproduce its 111035 verbatim.
//
// S1-S3 are checked AT EVERY STEP (violations recorded the moment the
// evidence exists — the failure witness is a prefix); S4 (completion) is
// the STOPPING/END condition, never a per-step invariant (design §4).
// The checker is integrated from raftharness/harness.go's checkSafety —
// same properties, same violation grammar, reshaped from fold-at-
// termination to per-step. The exercise floor (>=1 leader claim, >=1
// committed command) is reported separately from safety, as the go-run
// family does: a cluster that never elects anyone satisfies S1
// vacuously.
package main

import (
	"raft"
	pb "raftpb"
)

func u64(v uint64) *uint64 { return &v }

// itoa/utoa: plain-Go integer rendering for the trace (no fmt dependence
// — the trace is the observation both oracles must agree on byte for
// byte, so it leans on nothing but core language).
func utoa(v uint64) string {
	if v == 0 {
		return "0"
	}
	s := ""
	for v > 0 {
		s = string(rune('0'+int(v%10))) + s
		v /= 10
	}
	return s
}

func itoa(v int) string {
	if v < 0 {
		return "-" + utoa(uint64(-v))
	}
	return utoa(uint64(v))
}

// ---------------------------------------------------------------------------
// The harness Logger (design §5; the Q2 ruling's harness side).
// ---------------------------------------------------------------------------

// harnessLogger: eight empty bodies (nothing renders, so no fmt path
// runs) and four fixed-string panics — raft's own assertions
// (assertConfStatesEquivalent via Logger.Panic) keep their teeth; Fatal
// panics too, there being no os.Exit to model. STATELESS by design: no
// fields, so every method reads and writes nothing, its footprint is
// empty, and sharing ONE value across all n nodes cannot appear in any
// pairwise-disjointness obligation of the §6 shared-nothing reduction
// argument. A logger that buffered would be shared mutable state touched
// by every node on every event; if recording is ever needed it must be
// per node and §6's footprint check re-run.
type harnessLogger struct{}

func (l *harnessLogger) Debug(v ...any)                   {}
func (l *harnessLogger) Debugf(format string, v ...any)   {}
func (l *harnessLogger) Info(v ...any)                    {}
func (l *harnessLogger) Infof(format string, v ...any)    {}
func (l *harnessLogger) Warning(v ...any)                 {}
func (l *harnessLogger) Warningf(format string, v ...any) {}
func (l *harnessLogger) Error(v ...any)                   {}
func (l *harnessLogger) Errorf(format string, v ...any)   {}
func (l *harnessLogger) Fatal(v ...any)                   { panic("raftharness: Logger.Fatal") }
func (l *harnessLogger) Fatalf(format string, v ...any)   { panic("raftharness: Logger.Fatalf") }
func (l *harnessLogger) Panic(v ...any)                   { panic("raftharness: Logger.Panic") }
func (l *harnessLogger) Panicf(format string, v ...any)   { panic("raftharness: Logger.Panicf") }

// installed exactly once, before any cluster exists (probe entry points
// call installLogger first) — which is what keeps raftLoggerMu/raftLogger
// read-only during every run (§6 checklist item 1).
var twinLogger = &harnessLogger{}
var loggerInstalled = false

func installLogger() {
	if !loggerInstalled {
		raft.SetLogger(twinLogger) // seam 1: the six getLogger() sites
		loggerInstalled = true
	}
}

// ---------------------------------------------------------------------------
// The twin: nodes, the network multiset, the per-step checker.
// ---------------------------------------------------------------------------

type twinNode struct {
	id uint64
	rn *raft.RawNode
	st *raft.MemoryStorage

	// harness-observed state, updated ONLY from harvested Readys and
	// applies — this is the §7 state projection's source.
	term    uint64 // last harvested HardState.Term
	commit  uint64 // last harvested HardState.Commit
	state   raft.StateType
	applied uint64 // highest applied index
	lastTrm uint64 // last applied entry's term (S3)
	got     map[string]bool
}

type slot struct {
	term uint64
	data string
	node uint64
}

type twin struct {
	nodes []*twinNode
	net   []*pb.Message // the multiset, insertion-ordered
	live  []bool        // removal by index, never by shifting (§3)

	leaderOf   map[uint64]uint64 // S1: term -> claiming node
	byIndex    map[uint64]slot   // S2: index -> (term, data)
	claims     int
	committed  int // committed non-empty EntryNormal applies, all nodes
	violations int

	pending []string // the drop-and-retry client's command queue
	driven  []string // successfully proposed commands (S4 ranges over these)
	seq     int

	trace string
	halt  bool // a schedule error (not a safety violation) stops the run
}

func (t *twin) say(s string)  { t.trace += s }
func (t *twin) viol(s string) { t.violations++; t.trace += " !" + s }

func newTwin(n int, cmds int) *twin {
	t := &twin{
		leaderOf: make(map[uint64]uint64),
		byIndex:  make(map[uint64]slot),
	}
	for c := 0; c < cmds; c++ {
		t.seq++
		t.pending = append(t.pending, "c"+itoa(t.seq))
	}
	voters := []uint64{}
	for id := 1; id <= n; id++ {
		voters = append(voters, uint64(id))
	}
	for id := 1; id <= n; id++ {
		nd := &twinNode{id: uint64(id), got: make(map[string]bool)}
		nd.st = raft.NewMemoryStorage()
		if nd.st.ApplySnapshot(&pb.Snapshot{Metadata: &pb.SnapshotMetadata{
			Index:     u64(1),
			Term:      u64(1),
			ConfState: &pb.ConfState{Voters: voters},
		}}) != nil {
			t.halt = true
			t.say(" !harness: ApplySnapshot failed")
			return t
		}
		cfg := &raft.Config{
			ID:              uint64(id),
			ElectionTick:    10,
			HeartbeatTick:   1,
			Storage:         nd.st,
			MaxSizePerMsg:   1 << 20,
			MaxInflightMsgs: 256,
			Logger:          twinLogger, // seam 2, per node (design §5)
		}
		rn, err := raft.NewRawNode(cfg)
		if err != nil {
			t.halt = true
			t.say(" !harness: NewRawNode failed")
			return t
		}
		nd.rn = rn
		t.nodes = append(t.nodes, nd)
	}
	return t
}

// harvest runs the bundled Ready cycle to LOCAL quiescence (the recorded
// §2 narrowing; see the header). Returns the number of Ready rounds.
func (t *twin) harvest(nd *twinNode) int {
	rounds := 0
	for nd.rn.HasReady() {
		rounds++
		if rounds > 64 {
			t.halt = true
			t.viol("harness: harvest did not quiesce in 64 rounds")
			return rounds
		}
		rd := nd.rn.Ready()

		// persist BEFORE send (the Ready contract).
		if !raft.IsEmptyHardState(rd.HardState) {
			if nd.st.SetHardState(rd.HardState) != nil {
				t.halt = true
				t.viol("harness: SetHardState failed")
				return rounds
			}
			nd.term = rd.HardState.GetTerm()
			nd.commit = rd.HardState.GetCommit()
		}
		if len(rd.Entries) > 0 {
			if nd.st.Append(rd.Entries) != nil {
				t.halt = true
				t.viol("harness: Append failed")
				return rounds
			}
		}
		if !raft.IsEmptySnap(rd.Snapshot) {
			// Fail closed: the twin never compacts, so no snapshot can
			// legitimately arrive (raftharness finding, kept).
			t.halt = true
			t.viol("harness: unexpected snapshot")
			return rounds
		}

		// record (S1 at harvest: the claim source is a Ready carrying
		// SoftState.RaftState == StateLeader, per the go-run family).
		if rd.SoftState != nil {
			nd.state = rd.SoftState.RaftState
			if rd.SoftState.RaftState == raft.StateLeader {
				t.claims++
				prev, ok := t.leaderOf[nd.term]
				if ok && prev != nd.id {
					t.viol("S1 election safety: term " + utoa(nd.term) +
						" claimed by both node " + utoa(prev) +
						" and node " + utoa(nd.id))
				}
				t.leaderOf[nd.term] = nd.id
			}
		}

		// send: fold outbound messages into the multiset.
		for _, m := range rd.Messages {
			t.net = append(t.net, m)
			t.live = append(t.live, true)
		}

		// apply (S2 + S3 at apply time, where the evidence exists).
		for _, e := range rd.CommittedEntries {
			t.apply(nd, e)
		}

		nd.rn.Advance(rd)
	}
	return rounds
}

func (t *twin) apply(nd *twinNode, e *pb.Entry) {
	idx := e.GetIndex()
	trm := e.GetTerm()
	// S3 apply monotonicity: indexes strictly increase, terms never
	// decrease, per node.
	if idx <= nd.applied {
		t.viol("S3 monotonicity: node " + utoa(nd.id) + " applied index " +
			utoa(idx) + " after index " + utoa(nd.applied))
	}
	if trm < nd.lastTrm {
		t.viol("S3 monotonicity: node " + utoa(nd.id) + " applied term " +
			utoa(trm) + " after term " + utoa(nd.lastTrm))
	}
	nd.applied = idx
	nd.lastTrm = trm
	if e.GetType() != pb.EntryNormal {
		// v1 proposes no conf changes; an unmodeled entry type is an
		// anomaly, surfaced loudly (the go-run family's channel).
		t.viol("S3 anomaly: node " + utoa(nd.id) + " unmodeled entry type at index " + utoa(idx))
		return
	}
	if len(e.GetData()) == 0 {
		return // the leader's empty entry: applied-index only
	}
	data := string(e.GetData())
	nd.got[data] = true
	t.committed++
	// S2 log/apply agreement.
	if s, ok := t.byIndex[idx]; ok {
		if s.term != trm || s.data != data {
			t.viol("S2 agreement: index " + utoa(idx) + " is (term=" +
				utoa(s.term) + "," + s.data + ") on node " + utoa(s.node) +
				" but (term=" + utoa(trm) + "," + data + ") on node " + utoa(nd.id))
		}
	} else {
		t.byIndex[idx] = slot{term: trm, data: data, node: nd.id}
	}
}

// liveCount and the k-th live message to node i (deliver's naming).
func (t *twin) liveCount() int {
	c := 0
	for i := range t.net {
		if t.live[i] {
			c++
		}
	}
	return c
}

func (t *twin) pickFor(to uint64, k int) int {
	seen := 0
	for i := range t.net {
		if t.live[i] && t.net[i].GetTo() == to {
			if seen == k {
				return i
			}
			seen++
		}
	}
	return -1
}

func (t *twin) deliverIdx(i int) {
	m := t.net[i]
	t.live[i] = false // remove BEFORE stepping: delivered exactly once
	to := t.nodes[m.GetTo()-1]
	if err := to.rn.Step(m); err != nil {
		// A rejected step (e.g. a dropped forwarded proposal while
		// leaderless) is a legitimate outcome, traced, not a violation.
		t.say(" steperr")
	}
	t.harvest(to)
}

// ---------------------------------------------------------------------------
// Events.
// ---------------------------------------------------------------------------

const (
	opTick = iota
	opCampaign
	opPropose
	opDeliver   // node, k: the k-th live message addressed to node
	opDrain     // deliver-to-quiescence, insertion order (stabilize's ROLE, not its procedure — header)
	opDrainRev  // deliver-to-quiescence, reverse-insertion order
	opDrainSkip // node: drain everything NOT addressed to node (starvation)
)

type op struct {
	kind int
	node int
	k    int
}

func (t *twin) step(o op) {
	if t.halt {
		return
	}
	switch o.kind {
	case opTick:
		nd := t.nodes[o.node-1]
		t.say("tick" + itoa(o.node))
		nd.rn.Tick()
		t.harvest(nd)
	case opCampaign:
		nd := t.nodes[o.node-1]
		t.say("campaign" + itoa(o.node))
		if nd.rn.Campaign() != nil {
			t.say(" err")
		}
		t.harvest(nd)
	case opPropose:
		nd := t.nodes[o.node-1]
		t.say("propose" + itoa(o.node))
		if len(t.pending) == 0 {
			t.halt = true
			t.say(" !schedule: nothing pending")
			return
		}
		cmd := t.pending[0]
		// The drop-and-retry client (design §3): RawNode.Propose returns
		// an error (ErrProposalDropped while leaderless); the command
		// stays pending and a later propose event retries it.
		if err := nd.rn.Propose([]byte(cmd)); err != nil {
			t.say(" dropped")
		} else {
			t.say("=" + cmd)
			t.pending = t.pending[1:]
			t.driven = append(t.driven, cmd)
		}
		t.harvest(nd)
	case opDeliver:
		i := t.pickFor(uint64(o.node), o.k)
		t.say("deliver" + itoa(o.node) + "." + itoa(o.k))
		if i < 0 {
			t.halt = true
			t.say(" !schedule: no such message")
			return
		}
		t.deliverIdx(i)
	case opDrain:
		t.say("drain")
		for n := 0; n < 10000; n++ {
			i := -1
			for j := range t.net {
				if t.live[j] {
					i = j
					break
				}
			}
			if i < 0 {
				return
			}
			t.deliverIdx(i)
		}
		t.halt = true
		t.viol("harness: drain did not quiesce")
	case opDrainRev:
		t.say("drainRev")
		for n := 0; n < 10000; n++ {
			i := -1
			for j := len(t.net) - 1; j >= 0; j-- {
				if t.live[j] {
					i = j
					break
				}
			}
			if i < 0 {
				return
			}
			t.deliverIdx(i)
		}
		t.halt = true
		t.viol("harness: drainRev did not quiesce")
	case opDrainSkip:
		t.say("drainSkip" + itoa(o.node))
		for n := 0; n < 10000; n++ {
			i := -1
			for j := range t.net {
				if t.live[j] && t.net[j].GetTo() != uint64(o.node) {
					i = j
					break
				}
			}
			if i < 0 {
				return
			}
			t.deliverIdx(i)
		}
		t.halt = true
		t.viol("harness: drainSkip did not quiesce")
	}
}

func stateChar(s raft.StateType) string {
	switch s {
	case raft.StateFollower:
		return "F"
	case raft.StateCandidate:
		return "C"
	case raft.StateLeader:
		return "L"
	case raft.StatePreCandidate:
		return "P"
	}
	return "?"
}

// projection: the per-event state digest (design §7's canonical
// projection, over harness-observed state only).
func (t *twin) projection() string {
	s := " |"
	for _, nd := range t.nodes {
		s += stateChar(nd.state) + utoa(nd.term) + "/" + utoa(nd.commit) +
			"/" + utoa(nd.applied) + " "
	}
	return s + "net=" + itoa(t.liveCount())
}

// S4 (the END condition, not a per-step invariant): every node applied
// every successfully-driven command.
func (t *twin) complete() bool {
	for _, nd := range t.nodes {
		for _, c := range t.driven {
			if !nd.got[c] {
				return false
			}
		}
	}
	return true
}

type sched struct {
	name  string
	n     int // cluster size
	cmds  int // pending-queue size (= propose ops that should succeed)
	floor int // exercise floor: minimum leader claims
	ops   []op
}

func runSched(s sched) string {
	t := newTwin(s.n, s.cmds)
	t.say("[" + s.name + "]\n")
	for k, o := range s.ops {
		t.say("e" + itoa(k+1) + " ")
		t.step(o)
		t.say(t.projection() + "\n")
		if t.halt {
			break
		}
	}
	comp := 0
	if t.complete() && len(t.pending) == 0 {
		comp = 1
	}
	floorOK := 1
	if t.claims < s.floor || t.committed < 1 {
		// reported SEPARATELY from safety (design §4): a shortfall means
		// the schedule exercised too little, not that raft is unsafe.
		floorOK = 0
	}
	t.say("end viol=" + itoa(t.violations) + " claims=" + itoa(t.claims) +
		" committed=" + itoa(t.committed) + " complete=" + itoa(comp) +
		" floor=" + itoa(floorOK) + "\n")
	return t.trace
}

// ---------------------------------------------------------------------------
// The schedules (the input; hand-written, each with its intent).
// ---------------------------------------------------------------------------

// probeTwinSingle reproduces W4.1's THE-MOMENT drive (111035) through
// the NEW harness: same calls, same bundled harvest, same packing.
func probeTwinSingle() int {
	installLogger()
	t := newTwin(1, 1)
	nd := t.nodes[0]
	rounds := 0
	nd.rn.Tick()
	rounds += t.harvest(nd)
	if nd.rn.Campaign() != nil {
		return -3
	}
	rounds += t.harvest(nd)
	if nd.rn.Propose([]byte("x")) != nil {
		return -4
	}
	rounds += t.harvest(nd)
	if t.halt || t.violations != 0 {
		return -5
	}
	isLeader := 0
	if nd.state == raft.StateLeader {
		isLeader = 1
	}
	// committedNormal in the probe's packing counted non-empty normal
	// entries; the twin's t.committed is exactly that (n=1).
	term := int(nd.term)
	if term > 9 {
		term = 9
	}
	applied := int(nd.applied)
	if applied > 9 {
		applied = 9
	}
	return isLeader*100000 + term*10000 + t.committed*1000 + applied*10 + rounds
}

// probeTwinElect: the n=3 baseline family — election, proposal, commit,
// leader-side and follower-side (forwarded) proposals, a dropped
// proposal retried, and contended elections (S1's workout).
func probeTwinElect() string {
	installLogger()
	out := ""
	out += runSched(sched{name: "elect", n: 3, cmds: 0, floor: 1, ops: []op{
		{kind: opCampaign, node: 1},
		{kind: opDrain},
	}})
	out += runSched(sched{name: "elect-propose-commit", n: 3, cmds: 2, floor: 1, ops: []op{
		{kind: opPropose, node: 1}, // dropped: no leader yet (retried below)
		{kind: opCampaign, node: 1},
		{kind: opDrain},
		{kind: opPropose, node: 1},
		{kind: opDrain},
		{kind: opPropose, node: 1},
		{kind: opDrain},
	}})
	out += runSched(sched{name: "follower-propose", n: 3, cmds: 1, floor: 1, ops: []op{
		{kind: opCampaign, node: 1},
		{kind: opDrain},
		{kind: opPropose, node: 2}, // forwarded MsgProp through the multiset
		{kind: opDrain},
	}})
	out += runSched(sched{name: "dueling-candidates", n: 3, cmds: 1, floor: 1, ops: []op{
		{kind: opCampaign, node: 1},
		{kind: opCampaign, node: 2}, // same term, contended votes
		{kind: opDrain},
		{kind: opPropose, node: 3}, // forwarded to whoever won
		{kind: opDrain},
	}})
	return out
}

// probeTwinPerturb: the perturbation matrix — the SAME elect+propose
// flow under schedules that reorder deliveries (reverse order, mixed
// orders, explicit per-message picks, and an unboundedly-delayed vote).
func probeTwinPerturb() string {
	installLogger()
	out := ""
	out += runSched(sched{name: "perturb-rev", n: 3, cmds: 1, floor: 1, ops: []op{
		{kind: opCampaign, node: 1},
		{kind: opDrainRev},
		{kind: opPropose, node: 1},
		{kind: opDrainRev},
	}})
	out += runSched(sched{name: "perturb-mix", n: 3, cmds: 2, floor: 1, ops: []op{
		{kind: opCampaign, node: 1},
		{kind: opDrainRev},
		{kind: opPropose, node: 2},
		{kind: opDrain},
		{kind: opPropose, node: 1},
		{kind: opDrainRev},
		{kind: opDrain},
	}})
	// explicit picks: node 3 hears the vote request before node 2, and
	// 3's grant reaches the candidate before 2's — the reverse of the
	// baseline insertion order; the first proposal commits at quorum
	// {1,3} before node 2 hears of it.
	out += runSched(sched{name: "perturb-picks", n: 3, cmds: 1, floor: 1, ops: []op{
		{kind: opCampaign, node: 1},      // net: vote->2, vote->3
		{kind: opDeliver, node: 3, k: 0}, // 3 first
		{kind: opDeliver, node: 2, k: 0},
		{kind: opDeliver, node: 1, k: 0}, // 3's grant (inserted first): quorum {1,3}
		{kind: opDeliver, node: 1, k: 0}, // 2's late grant to the new leader
		{kind: opDrain},
		{kind: opPropose, node: 1},       // app->2, app->3
		{kind: opDeliver, node: 3, k: 0}, // 3 appends first
		{kind: opDeliver, node: 1, k: 0}, // 3's ack: commit at quorum {1,3}
		{kind: opDrain},
	}})
	// starve-node: everything addressed to node 3 sits in the multiset
	// for the whole run (delay without bound — the reliable-first
	// envelope's "not chosen yet" is a real schedule, not a drop; the
	// design's fairness non-assumption made concrete). SAFETY-ONLY by
	// construction: S4 completion is EXPECTED to fail (complete=0 —
	// node 3 never applies), while S1-S3 must hold throughout.
	out += runSched(sched{name: "starve-node", n: 3, cmds: 1, floor: 1, ops: []op{
		{kind: opCampaign, node: 1},
		{kind: opDrainSkip, node: 3}, // quorum {1,2} elects; 3 starved
		{kind: opPropose, node: 1},
		{kind: opDrainSkip, node: 3}, // commits on {1,2}; 3 still starved
	}})
	return out
}

// probeTwinTicks: heartbeat ticking exercised under the jitter-safe
// bound (per-node unreset election ticks stay far below ElectionTick=10,
// so the D-11 draw's value is never observable — the header's argument).
func probeTwinTicks() string {
	installLogger()
	out := ""
	out += runSched(sched{name: "heartbeat", n: 3, cmds: 1, floor: 1, ops: []op{
		{kind: opCampaign, node: 1},
		{kind: opDrain},
		{kind: opTick, node: 1}, // HeartbeatTick=1: emits heartbeats
		{kind: opDrain},
		{kind: opTick, node: 2}, // follower ticks: 1 election tick, harmless
		{kind: opTick, node: 3},
		{kind: opPropose, node: 1},
		{kind: opDrain},
		{kind: opTick, node: 1},
		{kind: opDrain},
	}})
	return out
}

