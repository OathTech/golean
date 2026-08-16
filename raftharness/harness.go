// The raft harness family: internally nondeterministic Go test cases that
// drive the real etcd-io/raft library (deps/raft) through an in-memory
// chaos network and assert raft's safety properties on termination.
//
// This is a Go programming exercise and an etcd-io/raft scaffolding /
// executable specification — it does NOT run through the golean frontend
// or interpreter. The machine-runnable twin is a later slice (see
// docs/2026-08-15_raft-push-p0-scoping.md).
//
// Network model: messages are delivered by one goroutine per copy, so
// delivery order is arbitrary even in the "reliable" configuration;
// scenarios additionally enable drops, duplication, bounded delay, and
// symmetric partitions. Raft is designed for exactly this envelope.
package main

import (
	"context"
	"fmt"
	"io"
	"log"
	"math/rand/v2"
	"sort"
	"sync"
	"time"

	"go.etcd.io/raft/v3"
	"go.etcd.io/raft/v3/raftpb"
	"google.golang.org/protobuf/proto"
)

// NetConfig is the chaos knob set for the in-memory network.
type NetConfig struct {
	DropProb float64
	DupProb  float64
	MaxDelay time.Duration
}

// AppliedEntry is one normal, non-empty entry as applied by a node's
// state machine, in apply order.
type AppliedEntry struct {
	Index uint64
	Term  uint64
	Data  string
}

// LeaderClaim records "node NodeID observed itself leader at term Term".
type LeaderClaim struct {
	NodeID uint64
	Term   uint64
}

type Cluster struct {
	mu      sync.Mutex
	nodes   map[uint64]*Node
	net     NetConfig
	blocked func(from, to uint64) bool // nil = no partition
	claims  []LeaderClaim

	rngMu sync.Mutex
	rng   *rand.Rand

	quiet raft.Logger
}

type Node struct {
	id      uint64
	c       *Cluster
	rn      raft.Node
	storage *raft.MemoryStorage
	inbox    chan *raftpb.Message
	stopCh   chan struct{}
	doneCh   chan struct{}
	stopOnce sync.Once
	ctx      context.Context // canceled on stop; bounds every rn.Step
	cancel   context.CancelFunc

	mu           sync.Mutex
	term         uint64 // last HardState term observed
	appliedIndex uint64 // last applied raft index (all entry types)
	applied      []AppliedEntry
	appliedSet   map[string]bool
	confState    *raftpb.ConfState // latest ApplyConfChange result; persisted on restart
	anomalies    []string          // fail-closed channel: impossible-path observations
}

func newCluster(n int, net NetConfig, seed uint64) *Cluster {
	c := &Cluster{
		nodes: make(map[uint64]*Node),
		net:   net,
		rng:   rand.New(rand.NewPCG(seed, seed^0x9e3779b97f4a7c15)),
		quiet: &raft.DefaultLogger{Logger: log.New(io.Discard, "", 0)},
	}
	var peers []raft.Peer
	for id := uint64(1); id <= uint64(n); id++ {
		peers = append(peers, raft.Peer{ID: id})
	}
	// Two-phase start: the nodes map must be complete before any app
	// loop runs, since loops read it without holding c.mu open-endedly
	// (audit find: a map write racing a live reader is a runtime throw).
	for id := uint64(1); id <= uint64(n); id++ {
		nd := c.newNode(id)
		nd.rn = raft.StartNode(c.config(id, nd.storage, 0), peers)
		c.nodes[id] = nd
	}
	for _, nd := range c.nodes {
		go nd.run()
	}
	return c
}

func (c *Cluster) newNode(id uint64) *Node {
	ctx, cancel := context.WithCancel(context.Background())
	return &Node{
		id:         id,
		c:          c,
		storage:    raft.NewMemoryStorage(),
		inbox:      make(chan *raftpb.Message, 1024),
		stopCh:     make(chan struct{}),
		doneCh:     make(chan struct{}),
		ctx:        ctx,
		cancel:     cancel,
		appliedSet: make(map[string]bool),
	}
}

func (c *Cluster) config(id uint64, st *raft.MemoryStorage, applied uint64) *raft.Config {
	return &raft.Config{
		ID:              id,
		ElectionTick:    10,
		HeartbeatTick:   1,
		Storage:         st,
		Applied:         applied,
		MaxSizePerMsg:   1 << 20,
		MaxInflightMsgs: 256,
		PreVote:         true,
		Logger:          c.quiet,
	}
}

func (c *Cluster) node(id uint64) *Node {
	c.mu.Lock()
	defer c.mu.Unlock()
	return c.nodes[id]
}

func (c *Cluster) ids() []uint64 {
	c.mu.Lock()
	defer c.mu.Unlock()
	var out []uint64
	for id := range c.nodes {
		out = append(out, id)
	}
	sort.Slice(out, func(i, j int) bool { return out[i] < out[j] })
	return out
}

func (c *Cluster) setNet(net NetConfig) {
	c.mu.Lock()
	defer c.mu.Unlock()
	c.net = net
}

// setPartition installs a symmetric partition: messages cross group
// boundaries never. nil groups heals.
func (c *Cluster) setPartition(groups [][]uint64) {
	c.mu.Lock()
	defer c.mu.Unlock()
	if groups == nil {
		c.blocked = nil
		return
	}
	groupOf := make(map[uint64]int)
	for gi, g := range groups {
		for _, id := range g {
			groupOf[id] = gi
		}
	}
	c.blocked = func(from, to uint64) bool {
		return groupOf[from] != groupOf[to]
	}
}

func (c *Cluster) recordClaim(id, term uint64) {
	c.mu.Lock()
	defer c.mu.Unlock()
	c.claims = append(c.claims, LeaderClaim{NodeID: id, Term: term})
}

func (c *Cluster) send(msgs []*raftpb.Message) {
	for _, m := range msgs {
		c.route(m)
	}
}

func (c *Cluster) route(m *raftpb.Message) {
	c.mu.Lock()
	blocked := c.blocked != nil && c.blocked(m.GetFrom(), m.GetTo())
	net := c.net
	to := c.nodes[m.GetTo()]
	c.mu.Unlock()
	if blocked || to == nil {
		return
	}
	copies := 1
	var delays [2]time.Duration
	c.rngMu.Lock()
	if net.DropProb > 0 && c.rng.Float64() < net.DropProb {
		c.rngMu.Unlock()
		return
	}
	if net.DupProb > 0 && c.rng.Float64() < net.DupProb {
		copies = 2
	}
	for i := 0; i < copies; i++ {
		if net.MaxDelay > 0 {
			delays[i] = time.Duration(c.rng.Int64N(int64(net.MaxDelay)))
		}
	}
	c.rngMu.Unlock()
	// Clone every extra copy BEFORE any delivery: a receiver's raft loop
	// mutates delivered proposal messages (node.go propc: m.From = ...),
	// so cloning after the first copy is in flight is a data race.
	msgs := make([]*raftpb.Message, copies)
	msgs[0] = m
	for i := 1; i < copies; i++ {
		msgs[i] = proto.Clone(m).(*raftpb.Message)
	}
	for i := 0; i < copies; i++ {
		go func(d time.Duration, msg *raftpb.Message) {
			if d > 0 {
				time.Sleep(d)
			}
			to.deliver(msg)
		}(delays[i], msgs[i])
	}
}

func (n *Node) deliver(m *raftpb.Message) {
	select {
	case n.inbox <- m:
	case <-n.stopCh:
	}
}

func (n *Node) run() {
	defer close(n.doneCh)
	ticker := time.NewTicker(2 * time.Millisecond)
	defer ticker.Stop()
	for {
		select {
		case <-ticker.C:
			n.rn.Tick()
		case rd := <-n.rn.Ready():
			// Durability contract: persist HardState and entries
			// BEFORE sending messages or applying.
			if !raft.IsEmptyHardState(rd.HardState) {
				if err := n.storage.SetHardState(rd.HardState); err != nil {
					panic(err)
				}
				n.mu.Lock()
				n.term = rd.HardState.GetTerm()
				n.mu.Unlock()
			}
			if err := n.storage.Append(rd.Entries); err != nil {
				panic(err)
			}
			if !raft.IsEmptySnap(rd.Snapshot) {
				// Fail closed: the harness never compacts, so no leader
				// can legitimately need to send a snapshot; silently
				// applying one would desync the recorded state machine.
				panic(fmt.Sprintf("node %d: unexpected snapshot (harness never compacts)", n.id))
			}
			if rd.SoftState != nil && rd.SoftState.RaftState == raft.StateLeader {
				n.mu.Lock()
				term := n.term
				n.mu.Unlock()
				n.c.recordClaim(n.id, term)
			}
			n.c.send(rd.Messages)
			for _, e := range rd.CommittedEntries {
				n.apply(e)
			}
			n.rn.Advance()
		case m := <-n.inbox:
			// A forwarded proposal (MsgProp) blocks inside raft until a
			// leader exists — stepping it on this loop would wedge ticks
			// (and thus elections) during leaderless windows. Step it off
			// the loop; n.ctx bounds it at node stop.
			if m.GetType() == raftpb.MessageType_MsgProp {
				go func(m *raftpb.Message) { _ = n.rn.Step(n.ctx, m) }(m)
			} else {
				_ = n.rn.Step(n.ctx, m)
			}
		case <-n.stopCh:
			n.rn.Stop()
			return
		}
	}
}

func (n *Node) apply(e *raftpb.Entry) {
	n.mu.Lock()
	defer n.mu.Unlock()
	if e.GetIndex() <= n.appliedIndex {
		// With Config.Applied set correctly on restart, a re-delivered
		// index is a raft or harness bug — record it loudly instead of
		// silently discarding the evidence (audit find: the silent
		// guard made S3-index unfalsifiable).
		n.anomalies = append(n.anomalies,
			fmt.Sprintf("node %d: re-delivered index %d (applied index already %d)", n.id, e.GetIndex(), n.appliedIndex))
		return
	}
	n.appliedIndex = e.GetIndex()
	switch e.GetType() {
	case raftpb.EntryType_EntryConfChange:
		cc := &raftpb.ConfChange{}
		if err := proto.Unmarshal(e.GetData(), cc); err != nil {
			panic(err)
		}
		n.confState = n.rn.ApplyConfChange(cc)
	case raftpb.EntryType_EntryConfChangeV2:
		cc := &raftpb.ConfChangeV2{}
		if err := proto.Unmarshal(e.GetData(), cc); err != nil {
			panic(err)
		}
		n.confState = n.rn.ApplyConfChange(cc)
	case raftpb.EntryType_EntryNormal:
		if len(e.GetData()) > 0 {
			n.applied = append(n.applied, AppliedEntry{Index: e.GetIndex(), Term: e.GetTerm(), Data: string(e.GetData())})
			n.appliedSet[string(e.GetData())] = true
		}
	default:
		// Fail closed on entry types this harness does not model.
		n.anomalies = append(n.anomalies,
			fmt.Sprintf("node %d: unmodeled entry type %v at index %d", n.id, e.GetType(), e.GetIndex()))
	}
}

func (n *Node) hasApplied(cmd string) bool {
	n.mu.Lock()
	defer n.mu.Unlock()
	return n.appliedSet[cmd]
}

func (n *Node) snapshotApplied() []AppliedEntry {
	n.mu.Lock()
	defer n.mu.Unlock()
	return append([]AppliedEntry(nil), n.applied...)
}

// stop halts the node's app loop and underlying raft node. Idempotent:
// failure paths may stop a victim node and then stopAll (audit find:
// the double close panicked the process on the budget-exhausted path).
func (n *Node) stop() {
	n.stopOnce.Do(func() {
		n.cancel()
		close(n.stopCh)
	})
	<-n.doneCh
}

// restartNode crash-restarts a node: the app loop is assumed stopped;
// raft state survives in its MemoryStorage (modeling durable storage),
// and the applied state machine survives (modeling a persistent SM).
//
// The membership ConfState MUST be persisted into the storage before
// RestartNode: RestartNode restores configuration from
// Storage.InitialState() = the snapshot metadata, and a node restarted
// with an empty ConfState has no voters, is never promotable, and can
// never campaign again (audit find #1 — the restarted node was
// silently config-less, so recovered-node-leads was never tested).
func (c *Cluster) restartNode(id uint64) {
	old := c.node(id)
	old.mu.Lock()
	appliedIndex := old.appliedIndex
	applied := old.applied
	appliedSet := old.appliedSet
	term := old.term
	confState := old.confState
	anomalies := old.anomalies
	old.mu.Unlock()

	if confState == nil {
		panic(fmt.Sprintf("node %d: restart with no recorded ConfState (bootstrap conf changes not applied?)", id))
	}
	if _, err := old.storage.CreateSnapshot(appliedIndex, confState, nil); err != nil {
		panic(fmt.Sprintf("node %d: persisting ConfState at index %d: %v", id, appliedIndex, err))
	}

	nd := c.newNode(id)
	nd.appliedIndex = appliedIndex
	nd.applied = applied
	nd.appliedSet = appliedSet
	nd.term = term
	nd.confState = confState
	nd.anomalies = anomalies
	nd.storage = old.storage
	nd.rn = raft.RestartNode(c.config(id, nd.storage, appliedIndex))

	c.mu.Lock()
	c.nodes[id] = nd
	c.mu.Unlock()
	go nd.run()
}

func (c *Cluster) stopAll() {
	for _, id := range c.ids() {
		c.node(id).stop()
	}
}

// ---------------------------------------------------------------------------
// The executable specification: what "raft is safe" means for this family.
// Checked on termination; every scenario must satisfy all of these on
// every run, under every interleaving and every chaos schedule.
// ---------------------------------------------------------------------------

// checkSafety returns a list of violation descriptions (empty = pass).
//
//	S1 Election Safety   — at most one leader per term; plus an
//	                       EXERCISE FLOOR: at least minClaims leader
//	                       claims must have been observed, so a scenario
//	                       that never exercises elections fails loudly
//	                       instead of passing vacuously.
//	S2 Log/Apply Agreement — no two nodes apply different (term, data)
//	                       at the same raft index (State Machine Safety,
//	                       observed at the apply boundary).
//	S3 Apply Monotonicity — per node, applied indexes strictly increase
//	                       and terms never decrease; re-delivered or
//	                       unmodeled entries are surfaced via the
//	                       per-node anomaly channel (recorded at apply
//	                       time, where the evidence exists).
//	S4 Completion        — every node applied every driven command.
//	                       Run even when the completion wait timed out,
//	                       so a timeout cannot mask a safety violation.
func (c *Cluster) checkSafety(allCmds []string, minClaims int) []string {
	var violations []string

	// S1: at most one leader per term.
	c.mu.Lock()
	claims := append([]LeaderClaim(nil), c.claims...)
	c.mu.Unlock()
	leaderOf := make(map[uint64]uint64)
	for _, cl := range claims {
		if prev, ok := leaderOf[cl.Term]; ok && prev != cl.NodeID {
			violations = append(violations,
				fmt.Sprintf("S1 election safety: term %d claimed by both node %d and node %d", cl.Term, prev, cl.NodeID))
		}
		leaderOf[cl.Term] = cl.NodeID
	}
	if len(claims) < minClaims {
		violations = append(violations,
			fmt.Sprintf("S1 exercise floor: only %d leader claim(s) observed, scenario requires >= %d", len(claims), minClaims))
	}

	// S3 anomaly channel (recorded at apply time).
	for _, id := range c.ids() {
		nd := c.node(id)
		nd.mu.Lock()
		anomalies := append([]string(nil), nd.anomalies...)
		nd.mu.Unlock()
		for _, a := range anomalies {
			violations = append(violations, "S3 anomaly: "+a)
		}
	}

	// S2 + S3 across all nodes.
	type slot struct {
		term uint64
		data string
		node uint64
	}
	byIndex := make(map[uint64]slot)
	for _, id := range c.ids() {
		entries := c.node(id).snapshotApplied()
		var prevIndex, prevTerm uint64
		for _, e := range entries {
			if e.Index <= prevIndex {
				violations = append(violations,
					fmt.Sprintf("S3 monotonicity: node %d applied index %d after index %d", id, e.Index, prevIndex))
			}
			if e.Term < prevTerm {
				violations = append(violations,
					fmt.Sprintf("S3 monotonicity: node %d applied term %d after term %d", id, e.Term, prevTerm))
			}
			prevIndex, prevTerm = e.Index, e.Term
			if s, ok := byIndex[e.Index]; ok {
				if s.term != e.Term || s.data != e.Data {
					violations = append(violations,
						fmt.Sprintf("S2 agreement: index %d is (term=%d,%q) on node %d but (term=%d,%q) on node %d",
							e.Index, s.term, s.data, s.node, e.Term, e.Data, id))
				}
			} else {
				byIndex[e.Index] = slot{term: e.Term, data: e.Data, node: id}
			}
		}
	}

	// S4: completion.
	for _, id := range c.ids() {
		nd := c.node(id)
		missing := 0
		for _, cmd := range allCmds {
			if !nd.hasApplied(cmd) {
				missing++
			}
		}
		if missing > 0 {
			violations = append(violations,
				fmt.Sprintf("S4 completion: node %d is missing %d of %d commands", id, missing, len(allCmds)))
		}
	}
	return violations
}

// ---------------------------------------------------------------------------
// Drivers.
// ---------------------------------------------------------------------------

// proposeAll drives cmds through node id until each is applied on that
// node, retrying dropped proposals (raft's client contract is
// at-least-once at this layer; the checker treats duplicates as ordinary
// entries all nodes must agree on).
func (c *Cluster) proposeAll(ctx context.Context, id uint64, cmds []string) error {
	for _, cmd := range cmds {
		for {
			if err := ctx.Err(); err != nil {
				return fmt.Errorf("budget exhausted proposing %q via node %d: %w", cmd, id, err)
			}
			nd := c.node(id)
			pctx, cancel := context.WithTimeout(ctx, 200*time.Millisecond)
			_ = nd.rn.Propose(pctx, []byte(cmd)) // errors (no leader, dropped) are retried
			cancel()
			if c.waitApplied(ctx, id, cmd, 500*time.Millisecond) {
				break
			}
		}
	}
	return nil
}

func (c *Cluster) waitApplied(ctx context.Context, id uint64, cmd string, budget time.Duration) bool {
	deadline := time.Now().Add(budget)
	for time.Now().Before(deadline) && ctx.Err() == nil {
		if c.node(id).hasApplied(cmd) {
			return true
		}
		time.Sleep(5 * time.Millisecond)
	}
	return c.node(id).hasApplied(cmd)
}

// waitAllApplied blocks until every node has applied every command.
func (c *Cluster) waitAllApplied(ctx context.Context, cmds []string) error {
	for {
		if err := ctx.Err(); err != nil {
			var lag []string
			for _, id := range c.ids() {
				missing := 0
				for _, cmd := range cmds {
					if !c.node(id).hasApplied(cmd) {
						missing++
					}
				}
				if missing > 0 {
					lag = append(lag, fmt.Sprintf("node %d missing %d", id, missing))
				}
			}
			return fmt.Errorf("budget exhausted waiting for full replication (%s): %w", joinStrings(lag), err)
		}
		done := true
		for _, id := range c.ids() {
			for _, cmd := range cmds {
				if !c.node(id).hasApplied(cmd) {
					done = false
					break
				}
			}
			if !done {
				break
			}
		}
		if done {
			return nil
		}
		time.Sleep(5 * time.Millisecond)
	}
}

func joinStrings(xs []string) string {
	out := ""
	for i, x := range xs {
		if i > 0 {
			out += ", "
		}
		out += x
	}
	return out
}
