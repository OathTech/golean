package main

import (
	"context"
	"fmt"
	"strings"
	"sync"
	"time"
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

func cmdBatch(seed uint64, proposer uint64, n int) []string {
	out := make([]string, n)
	for i := range out {
		out[i] = fmt.Sprintf("s%x-n%d-c%d", seed, proposer, i)
	}
	return out
}

// finish heals nothing (callers heal first when needed), waits for full
// replication of cmds, stops the cluster, and runs the safety checker.
func finish(ctx context.Context, c *Cluster, cmds []string) error {
	err := c.waitAllApplied(ctx, cmds)
	c.stopAll()
	if err != nil {
		return err
	}
	if v := c.checkSafety(cmds); len(v) > 0 {
		return fmt.Errorf("SAFETY VIOLATIONS:\n  %s", strings.Join(v, "\n  "))
	}
	return nil
}

// basic: 3 nodes, no injected chaos (delivery order is still arbitrary —
// one goroutine per message), one proposer, 20 commands.
func runBasic(ctx context.Context, seed uint64) error {
	c := newCluster(3, NetConfig{}, seed)
	cmds := cmdBatch(seed, 1, 20)
	if err := c.proposeAll(ctx, 1, cmds); err != nil {
		c.stopAll()
		return err
	}
	return finish(ctx, c, cmds)
}

// reorder-dup: 3 nodes, 10% duplication and up to 3ms random delay
// (heavy reordering), every node proposes concurrently.
func runReorderDup(ctx context.Context, seed uint64) error {
	c := newCluster(3, NetConfig{DupProb: 0.10, MaxDelay: 3 * time.Millisecond}, seed)
	return driveConcurrent(ctx, c, seed, 5, NetConfig{})
}

// chaos: 5 nodes, 15% drops + 5% duplication + delay, every node
// proposes concurrently; the network heals before the completion wait
// (S4 is only demanded of a healed network — the conditioned-liveness
// shape from the scoping doc).
func runChaos(ctx context.Context, seed uint64) error {
	c := newCluster(5, NetConfig{DropProb: 0.15, DupProb: 0.05, MaxDelay: 3 * time.Millisecond}, seed)
	return driveConcurrent(ctx, c, seed, 6, NetConfig{})
}

// driveConcurrent has every node propose its own batch concurrently,
// then sets the network to healNet and finishes.
func driveConcurrent(ctx context.Context, c *Cluster, seed uint64, perNode int, healNet NetConfig) error {
	ids := c.ids()
	var all []string
	batches := make(map[uint64][]string)
	for _, id := range ids {
		b := cmdBatch(seed, id, perNode)
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
	c.setNet(healNet)
	return finish(ctx, c, all)
}

// partition: 5 nodes; commands flow, then a 2|3 partition. The majority
// side keeps committing; proposals driven into the minority side must
// not be lost OR double-committed — they land after heal. This is the
// member most likely to catch an election-safety or agreement violation
// if one existed.
func runPartition(ctx context.Context, seed uint64) error {
	c := newCluster(5, NetConfig{MaxDelay: time.Millisecond}, seed)
	pre := cmdBatch(seed, 1, 5)
	if err := c.proposeAll(ctx, 1, pre); err != nil {
		c.stopAll()
		return err
	}

	c.setPartition([][]uint64{{1, 2}, {3, 4, 5}})

	// Minority-side proposals: these spin (retrying) until the heal,
	// then must commit exactly like any other command.
	minority := cmdBatch(seed, 2, 3)
	minorityDone := make(chan error, 1)
	go func() { minorityDone <- c.proposeAll(ctx, 2, minority) }()

	// Majority side must make progress DURING the partition.
	majority := cmdBatch(seed, 3, 5)
	if err := c.proposeAll(ctx, 3, majority); err != nil {
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
	return finish(ctx, c, all)
}

// leader-churn: 3 nodes; a churner forces a leadership transfer every
// 100ms while 20 commands are driven. Exercises the (term, leader)
// claim stream — S1's main workout besides partition.
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
			case <-time.After(100 * time.Millisecond):
			}
			st := c.node(1).rn.Status()
			if st.Lead == 0 {
				continue
			}
			transferee := st.Lead%3 + 1
			c.node(st.Lead).rn.TransferLeadership(ctx, st.Lead, transferee)
		}
	}()
	cmds := cmdBatch(seed, 1, 20)
	err := c.proposeAll(ctx, 1, cmds)
	close(churnStop)
	churnWG.Wait()
	if err != nil {
		c.stopAll()
		return err
	}
	return finish(ctx, c, cmds)
}

// crash-restart: 3 nodes; a victim (the leader on odd seeds, a follower
// on even) is crashed mid-run and restarted from its persisted state.
// Exercises the durability half of the safety argument: nothing
// committed may be lost across the crash.
func runCrashRestart(ctx context.Context, seed uint64) error {
	c := newCluster(3, NetConfig{}, seed)
	pre := cmdBatch(seed, 1, 8)
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
	mid := cmdBatch(seed, proposer, 6)
	if err := c.proposeAll(ctx, proposer, mid); err != nil {
		c.stopAll()
		return err
	}

	c.restartNode(victim)

	post := cmdBatch(seed, victim, 6)
	if err := c.proposeAll(ctx, victim, post); err != nil {
		c.stopAll()
		return err
	}
	all := append(append(pre, mid...), post...)
	return finish(ctx, c, all)
}
