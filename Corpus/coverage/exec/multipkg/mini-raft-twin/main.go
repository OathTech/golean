package main

// The mini-raft twin family (W4.3 item 4 — the W4.2 owed corpus rows:
// "the twin as a corpus family" + "the perturbation schedules as
// corpus rows"; docs/raft-w43-log.md). A schedule-driven 3-node driver
// over the mnode/mpb miniature: a message BAG with removal by index
// ("delay" is "not chosen yet"), drain / reverse-drain / explicit-pick
// / starvation schedules, S1–S3 checked at every step and S4 at the
// end (the harness design §4 shape). Each subject returns a compact
// deterministic trace + verdicts; the differential pins it under both
// oracles. Starvation is the conditioned-safety pin: S1–S3 hold while
// S4 stays incomplete BY DESIGN on the starved node.

import (
	"mnode"
	"mpb"
)

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

type driver struct {
	nodes []*mnode.Node
	bag   []*mpb.Message
	live  []bool

	leaderOf map[uint64]uint64   // S1: term -> leader id
	byIndex  map[int]string      // S2: applied index -> "term/data"
	trace    string
	viols    int
}

func newDriver(n int) *driver {
	d := &driver{leaderOf: map[uint64]uint64{}, byIndex: map[int]string{}}
	for id := uint64(1); id <= uint64(n); id++ {
		d.nodes = append(d.nodes, mnode.New(id, n))
	}
	return d
}

func (d *driver) send(ms []*mpb.Message) {
	for _, m := range ms {
		d.bag = append(d.bag, m)
		d.live = append(d.live, true)
	}
}

// check runs S1-S3 after every event (the per-step invariant form).
func (d *driver) check() {
	for _, nd := range d.nodes {
		if nd.State == mnode.Leader {
			if prev, ok := d.leaderOf[nd.Term]; ok && prev != nd.ID {
				d.viols++
				d.trace += " !S1"
			} else {
				d.leaderOf[nd.Term] = nd.ID
			}
		}
		for i, data := range nd.Applied {
			key := utoa(nd.Log[i].Term) + "/" + data
			if prev, ok := d.byIndex[i]; ok && prev != key {
				d.viols++
				d.trace += " !S2"
			} else {
				d.byIndex[i] = key
			}
		}
		// S3 (apply monotonicity) is structural here: Applied only
		// grows by construction; its length regressing would be a
		// driver bug — assert it via commit<=len(log).
		if nd.Commit > uint64(len(nd.Log)) {
			d.viols++
			d.trace += " !S3"
		}
	}
}

func (d *driver) campaign(i int) {
	d.send(d.nodes[i-1].Campaign())
	d.check()
}

func (d *driver) propose(i int, data string) bool {
	ms, ok := d.nodes[i-1].Propose(data)
	d.send(ms)
	d.check()
	return ok
}

func (d *driver) deliver(k int) {
	if k >= len(d.bag) || !d.live[k] {
		return
	}
	d.live[k] = false
	m := d.bag[k]
	d.send(d.nodes[m.To-1].Step(m))
	d.check()
}

// drain delivers to quiescence in insertion order (rev=false) or
// reverse-insertion order (rev=true), skipping node `skip` (0 = none):
// the drain/drainRev/drainSkip macros of the twin's vocabulary.
func (d *driver) drain(rev bool, skip uint64) {
	for round := 0; round < 10000; round++ {
		idx := -1
		if !rev {
			for k := 0; k < len(d.bag); k++ {
				if d.live[k] && d.bag[k].To != skip {
					idx = k
					break
				}
			}
		} else {
			for k := len(d.bag) - 1; k >= 0; k-- {
				if d.live[k] && d.bag[k].To != skip {
					idx = k
					break
				}
			}
		}
		if idx < 0 {
			return
		}
		d.deliver(idx)
	}
}

func (d *driver) snap() string {
	s := "|"
	for _, nd := range d.nodes {
		s += nd.State.Char() + utoa(nd.Term) + "/" + utoa(nd.Commit) +
			"/" + utoa(uint64(len(nd.Applied))) + " "
	}
	return s
}

// s4 reports completion: every node applied every command in cmds.
func (d *driver) s4(cmds int) string {
	done := 0
	for _, nd := range d.nodes {
		if len(nd.Applied) == cmds {
			done++
		}
	}
	return "s4=" + utoa(uint64(done)) + "/" + utoa(uint64(len(d.nodes)))
}

func twinElectProposeCommit() string {
	d := newDriver(3)
	d.campaign(1)
	d.drain(false, 0)
	d.trace += d.snap()
	if !d.propose(1, "x1") {
		d.trace += " drop"
	}
	d.drain(false, 0)
	d.propose(1, "x2")
	d.drain(false, 0)
	d.trace += d.snap() + " " + d.s4(2) + " viol=" + utoa(uint64(d.viols))
	return d.trace
}

func twinPerturbRev() string {
	d := newDriver(3)
	d.campaign(1)
	d.drain(true, 0)
	d.propose(1, "y1")
	d.drain(true, 0)
	d.trace += d.snap() + " " + d.s4(1) + " viol=" + utoa(uint64(d.viols))
	return d.trace
}

func twinPerturbPicks() string {
	d := newDriver(3)
	d.campaign(1)
	// node 3 hears the vote first; commit reached at quorum {1,3}.
	d.deliver(1) // vote req to 3
	d.deliver(3) // 3's grant (bag: [v2,v3,g3] -> indices 0,1 then resp appended)
	d.deliver(0) // vote req to 2
	d.drain(false, 0)
	d.propose(1, "z1")
	d.drain(false, 2)
	d.trace += d.snap() + " " + d.s4(1) + " viol=" + utoa(uint64(d.viols))
	return d.trace
}

func twinStarveNode() string {
	d := newDriver(3)
	d.campaign(1)
	d.drain(false, 3)
	d.propose(1, "w1")
	d.propose(1, "w2")
	d.drain(false, 3)
	// S1-S3 hold; S4 is 2/3 EXPECTED (node 3 starved for the whole
	// run — conditioned safety made concrete).
	d.trace += d.snap() + " " + d.s4(2) + " viol=" + utoa(uint64(d.viols))
	return d.trace
}

// twinDuel: two candidates in the same term window — S1's workout.
func twinDuel() string {
	d := newDriver(3)
	d.campaign(1)
	d.campaign(2) // same term on both candidates
	d.drain(false, 0)
	d.trace += d.snap() + " viol=" + utoa(uint64(d.viols))
	return d.trace
}

// twinChoiceOrder is the CHOICE-STREAM membership row (the W4.2 owed
// row "a membership row for the choice-stream-driven twin"): which of
// the two vote requests a fresh campaign emits is delivered first is
// drawn from the machine's choice stream via the map-iteration pick
// (the D-11 idiom); under go run, Go's own randomized iteration
// samples the same set. KEPT MINIMAL on purpose: the membership
// enumerator re-executes per stream probe, so the certified program is
// the two-node kernel of the twin shape (Campaign -> pick -> Step),
// not the full driver — the full-driver form exceeded the enumerator's
// work cap honestly and is pinned by the strict rows instead.
func twinChoiceOrder() int {
	n1 := mnode.New(1, 3)
	msgs := n1.Campaign() // [vote->2, vote->3]
	pick := make(map[int]struct{}, 2)
	for i := 0; i < 2; i++ {
		pick[i] = struct{}{}
	}
	first := 0
	for k := range pick {
		first = k
		break
	}
	m := msgs[first]
	recv := mnode.New(m.To, 3)
	resp := recv.Step(m)
	granted := 0
	if len(resp) == 1 && resp[0].Granted {
		granted = 1
	}
	return int(m.To)*10 + granted
}

func main() {
	println(twinElectProposeCommit(), twinPerturbRev(), twinPerturbPicks(),
		twinStarveNode(), twinDuel(), twinChoiceOrder())
}
