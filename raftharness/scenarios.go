package main

import (
	"context"
	"fmt"
	"strings"
	"sync"
	"time"

	"go.etcd.io/raft/v3"
)

// A Scenario is one family member: an internally nondeterministic run
// that must satisfy the executable specification (checkSafety) on every
// termination, under every interleaving, chaos schedule, and seed.
type Scenario struct {
	Name   string
	Budget time.Duration
	Run    func(ctx context.Context, seed uint64) error
}

var scenarios = []Scenario{
	{"basic", 60 * time.Second, runBasic},
	{"reorder-dup", 60 * time.Second, runReorderDup},
	{"chaos", 120 * time.Second, runChaos},
	{"partition", 120 * time.Second, runPartition},
	{"leader-churn", 120 * time.Second, runLeaderChurn},
	{"crash-restart", 120 * time.Second, runCrashRestart},
}

// cmdBatch names commands by seed + a PHASE TAG + index. The tag must
// be unique per batch within a scenario: command identity is the data
// string, and a colliding batch is self-satisfying — proposeAll sees
// hasApplied(cmd) immediately and the whole phase becomes a no-op
// (audit find #3: crash-restart's mid/post phases collided with pre
// on 2/3 of seeds).
func cmdBatch(seed uint64, tag string, n int) []string {
	out := make([]string, n)
	for i := range out {
		out[i] = fmt.Sprintf("s%x-%s-c%d", seed, tag, i)
	}
	return out
}

// finish heals nothing (callers heal first when needed), waits for full
// replication of cmds, stops the cluster, and runs the safety checker.
// The checker runs EVEN IF the completion wait timed out — a liveness
// failure must not mask a safety violation (audit find #2: the early
// return made checkSafety unreachable on the timeout path, and made
// the S4 clause a restatement of a check that had already passed).
func finish(ctx context.Context, c *Cluster, cmds []string, minClaims int) error {
	waitErr := c.waitAllApplied(ctx, cmds)
	c.stopAll()
	if v := c.checkSafety(cmds, minClaims); len(v) > 0 {
		msg := fmt.Sprintf("SAFETY VIOLATIONS:\n  %s", strings.Join(v, "\n  "))
		if waitErr != nil {
			msg += fmt.Sprintf("\n  (and completion wait failed: %v)", waitErr)
		}
		return fmt.Errorf("%s", msg)
	}
	return waitErr
}

// basic: 3 nodes, no injected chaos (delivery order is still arbitrary —
// one goroutine per message), one proposer, 20 commands.
func runBasic(ctx context.Context, seed uint64) error {
	c := newCluster(3, NetConfig{}, seed)
	cmds := cmdBatch(seed, "basic", 20)
	if err := c.proposeAll(ctx, 1, cmds); err != nil {
		c.stopAll()
		return err
	}
	return finish(ctx, c, cmds, 1)
}

// reorder-dup: 3 nodes, 10% duplication and up to 3ms random delay
// (heavy reordering), every node proposes concurrently.
func runReorderDup(ctx context.Context, seed uint64) error {
	c := newCluster(3, NetConfig{DupProb: 0.10, MaxDelay: 3 * time.Millisecond}, seed)
	return driveConcurrent(ctx, c, seed, 5, NetConfig{}, 1, nil)
}

// chaos: 5 nodes, 15% drops + 5% duplication + delay, every node
// proposes concurrently; the network heals before the completion wait
// (S4 is only demanded of a healed network — the conditioned-liveness
// shape from the scoping doc). A mid-run leader-isolation pulse forces
// a real re-election: message-level chaos alone cannot (heartbeats
// every ~2ms against a 20-40ms election timeout never time out under
// 15% independent drops — audit find #5), so without the pulse S1 was
// checking a one-claim stream.
func runChaos(ctx context.Context, seed uint64) error {
	c := newCluster(5, NetConfig{DropProb: 0.15, DupProb: 0.05, MaxDelay: 3 * time.Millisecond}, seed)
	pulseDone := make(chan struct{})
	go func() {
		defer close(pulseDone)
		deadline := time.Now().Add(2 * time.Second)
		for time.Now().Before(deadline) && ctx.Err() == nil {
			st := c.node(1).rn.Status()
			if st.Lead != 0 {
				var rest []uint64
				for _, id := range c.ids() {
					if id != st.Lead {
						rest = append(rest, id)
					}
				}
				c.setPartition([][]uint64{{st.Lead}, rest})
				time.Sleep(150 * time.Millisecond)
				c.setPartition(nil)
				return
			}
			time.Sleep(20 * time.Millisecond)
		}
	}()
	return driveConcurrent(ctx, c, seed, 6, NetConfig{}, 2, pulseDone)
}

// driveConcurrent has every node propose its own batch concurrently,
// waits for barrier (if non-nil; e.g. a chaos pulse that must not
// outlive the run), then sets the network to healNet and finishes.
func driveConcurrent(ctx context.Context, c *Cluster, seed uint64, perNode int, healNet NetConfig, minClaims int, barrier <-chan struct{}) error {
	ids := c.ids()
	var all []string
	batches := make(map[uint64][]string)
	for _, id := range ids {
		b := cmdBatch(seed, fmt.Sprintf("n%d", id), perNode)
		batches[id] = b
		all = append(all, b...)
	}
	errs := make(chan error, len(ids))
	var wg sync.WaitGroup
	for _, id := range ids {
		wg.Add(1)
		go func(id uint64) {
			defer wg.Done()
			errs <- c.proposeAll(ctx, id, batches[id])
		}(id)
	}
	wg.Wait()
	close(errs)
	for err := range errs {
		if err != nil {
			c.stopAll()
			return err
		}
	}
	if barrier != nil {
		<-barrier
	}
	c.setNet(healNet)
	return finish(ctx, c, all, minClaims)
}

// partition: 5 nodes; commands flow, then the CURRENT LEADER is
// partitioned into a 2-node minority (leader placement chosen so the
// majority must elect a fresh leader in a higher term — a static
// grouping only forces an election on the seeds where the leader
// happened to land in the minority; audit find: partition sometimes
// yielded a single leader claim). The majority keeps committing;
// proposals driven into the deposed leader must survive the heal
// without conflicting with majority commits (S2 is the double-commit
// detector: same index, different data). This is the member most
// likely to catch an election-safety or agreement violation.
func runPartition(ctx context.Context, seed uint64) error {
	c := newCluster(5, NetConfig{MaxDelay: time.Millisecond}, seed)
	pre := cmdBatch(seed, "pre", 5)
	if err := c.proposeAll(ctx, 1, pre); err != nil {
		c.stopAll()
		return err
	}

	lead := c.node(1).rn.Status().Lead
	if lead == 0 {
		lead = 1 // no known leader (possible but unlikely post-pre); any grouping still partitions
	}
	buddy := lead%5 + 1
	var majoritySide []uint64
	for _, id := range c.ids() {
		if id != lead && id != buddy {
			majoritySide = append(majoritySide, id)
		}
	}
	c.setPartition([][]uint64{{lead, buddy}, majoritySide})

	// Minority-side proposals into the deposed leader: these spin
	// (retrying) until the heal, then must commit like any command.
	minority := cmdBatch(seed, "min", 3)
	minorityDone := make(chan error, 1)
	go func() { minorityDone <- c.proposeAll(ctx, lead, minority) }()

	// The majority side must elect and make progress DURING the
	// partition.
	majority := cmdBatch(seed, "maj", 5)
	if err := c.proposeAll(ctx, majoritySide[0], majority); err != nil {
		c.stopAll()
		return err
	}

	time.Sleep(500 * time.Millisecond) // let the partition bite
	c.setPartition(nil)                // heal

	if err := <-minorityDone; err != nil {
		c.stopAll()
		return err
	}
	all := append(append(pre, minority...), majority...)
	return finish(ctx, c, all, 2)
}

// leader-churn: 3 nodes; a churner forces a leadership transfer every
// 25ms while 40 commands are driven. Exercises the (term, leader)
// claim stream — S1's main workout besides partition. (The original
// 100ms-interval/20-command calibration usually issued a single
// transfer before the drive completed — audit find #5; the exercise
// floor in finish now guards this from regressing.)
func runLeaderChurn(ctx context.Context, seed uint64) error {
	c := newCluster(3, NetConfig{MaxDelay: time.Millisecond}, seed)
	churnStop := make(chan struct{})
	var churnWG sync.WaitGroup
	churnWG.Add(1)
	go func() {
		defer churnWG.Done()
		for {
			select {
			case <-churnStop:
				return
			case <-time.After(25 * time.Millisecond):
			}
			st := c.node(1).rn.Status()
			if st.Lead == 0 {
				continue
			}
			transferee := st.Lead%3 + 1
			c.node(st.Lead).rn.TransferLeadership(ctx, st.Lead, transferee)
		}
	}()
	cmds := cmdBatch(seed, "churn", 40)
	err := c.proposeAll(ctx, 1, cmds)
	close(churnStop)
	churnWG.Wait()
	if err != nil {
		c.stopAll()
		return err
	}
	return finish(ctx, c, cmds, 2)
}

// crash-restart: 3 nodes; a victim (the leader on odd seeds, a follower
// on even) is crashed mid-run and restarted from its persisted state.
// Exercises the durability half of the safety argument: nothing
// committed may be lost across the crash, and — the property proper —
// the RECOVERED node must be able to win an election on its restored
// state and then commit (audit find #1: before the ConfState-persist
// fix, restarted nodes were silently config-less and unpromotable, so
// this was never tested).
func runCrashRestart(ctx context.Context, seed uint64) error {
	c := newCluster(3, NetConfig{}, seed)
	pre := cmdBatch(seed, "pre", 8)
	if err := c.proposeAll(ctx, 1, pre); err != nil {
		c.stopAll()
		return err
	}

	victim := c.node(1).rn.Status().Lead
	if victim == 0 || seed%2 == 0 {
		victim = victim%3 + 1 // a non-leader (or arbitrary if unknown)
	}
	c.node(victim).stop()

	proposer := victim%3 + 1
	mid := cmdBatch(seed, "mid", 6)
	if err := c.proposeAll(ctx, proposer, mid); err != nil {
		c.stopAll()
		return err
	}

	c.restartNode(victim)

	// The recovered node must be able to LEAD on its restored state.
	deadline := time.Now().Add(5 * time.Second)
	for {
		if ctx.Err() != nil || time.Now().After(deadline) {
			c.stopAll()
			return fmt.Errorf("restarted node %d never regained leadership", victim)
		}
		st := c.node(victim).rn.Status()
		if st.RaftState == raft.StateLeader {
			break
		}
		if st.Lead != 0 && st.Lead != victim {
			c.node(st.Lead).rn.TransferLeadership(ctx, st.Lead, victim)
		}
		time.Sleep(50 * time.Millisecond)
	}

	post := cmdBatch(seed, "post", 6)
	if err := c.proposeAll(ctx, victim, post); err != nil {
		c.stopAll()
		return err
	}
	all := append(append(pre, mid...), post...)
	return finish(ctx, c, all, 2)
}
