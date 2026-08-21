// The datadriven-trace REPLAY ENV (W4.2 item 3 — the harness design §7's
// command-sequence reading of upstream's testdata, ok-tier;
// docs/raft-w42-log.md item 3).
//
// A faithful plain-Go mirror of deps/raft/rafttest's InteractionEnv for
// the SUPPORTED command subset: RawNode per node, a message BAG
// (delivery removes in bag order, upstream's splitMsgs), process-ready
// as ONE Ready cycle (persist -> apply -> route -> Advance, upstream's
// ProcessReady order), stabilize as upstream's ready/deliver fixed
// point. Config defaults are upstream's raftConfigStub (ElectionTick 3,
// HeartbeatTick 1, no size limits). NOT the twin: the twin
// (twin-main.go) is the harness whose schedule is the input; this env
// exists to REPLAY upstream's command sequences and is measurement
// tooling, not a corpus landing.
//
// The observation is a trace string: per block, the command verdict
// (ok / err / a fail-closed stop note) plus the state projection —
// compared byte-for-byte between `go run` and the machine by
// tracereplay.py, which also scores the ok-expectation blocks against
// upstream's expected output.
//
// This file is package-main LIBRARY source: tracereplay.py copies it
// beside a GENERATED main.go (the parsed command sequence of one trace)
// into a scratch program. It compiles on its own only together with
// such a main.
package main

import (
	"raft"
	pb "raftpb"
)

func u64p(v uint64) *uint64 { return &v }

func rutoa(v uint64) string {
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

func ritoa(v int) string {
	if v < 0 {
		return "-" + rutoa(uint64(-v))
	}
	return rutoa(uint64(v))
}

// replayLogger: the same stateless harness logger as the twin's (design
// §5): eight empty bodies, four fixed-string panics.
type replayLogger struct{}

func (l *replayLogger) Debug(v ...any)                   {}
func (l *replayLogger) Debugf(format string, v ...any)   {}
func (l *replayLogger) Info(v ...any)                    {}
func (l *replayLogger) Infof(format string, v ...any)    {}
func (l *replayLogger) Warning(v ...any)                 {}
func (l *replayLogger) Warningf(format string, v ...any) {}
func (l *replayLogger) Error(v ...any)                   {}
func (l *replayLogger) Errorf(format string, v ...any)   {}
func (l *replayLogger) Fatal(v ...any)                   { panic("replayenv: Logger.Fatal") }
func (l *replayLogger) Fatalf(format string, v ...any)   { panic("replayenv: Logger.Fatalf") }
func (l *replayLogger) Panic(v ...any)                   { panic("replayenv: Logger.Panic") }
func (l *replayLogger) Panicf(format string, v ...any)   { panic("replayenv: Logger.Panicf") }

type envNode struct {
	rn *raft.RawNode
	st *raft.MemoryStorage

	// harness-observed projection state (same sourcing as the twin's).
	term    uint64
	commit  uint64
	state   raft.StateType
	applied uint64
}

type renv struct {
	lg    *replayLogger
	nodes []*envNode
	msgs  []*pb.Message // the bag; delivery removes, order-preserving
	trace string
	halt  bool // a fail-closed replay stop (recorded, ends the run)
}

func newEnv() *renv {
	e := &renv{lg: &replayLogger{}}
	raft.SetLogger(e.lg)
	return e
}

func (e *renv) say(s string) { e.trace += s }

func (e *renv) stop(why string) {
	e.halt = true
	e.say(" STOP:" + why)
}

func stChar(s raft.StateType) string {
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

func (e *renv) projection() string {
	s := " |"
	for _, nd := range e.nodes {
		s += stChar(nd.state) + rutoa(nd.term) + "/" + rutoa(nd.commit) +
			"/" + rutoa(nd.applied) + " "
	}
	return s + "bag=" + ritoa(len(e.msgs))
}

// addNodes mirrors upstream AddNodes + raftConfigStub: n fresh nodes,
// ids continuing the sequence, snapshot-seeded iff index/voters given
// (upstream requires index > 1 then, and stamps Metadata.Term = 1).
func (e *renv) addNodes(n int, voters []uint64, learners []uint64, index uint64,
	prevote bool, checkquorum bool, inflight int, maxCommittedSize uint64,
	stepDownOnRemoval bool, disableCCV bool) bool {
	bootstrap := len(voters) > 0 || len(learners) > 0 || index > 0
	for i := 0; i < n; i++ {
		id := uint64(1 + len(e.nodes))
		st := raft.NewMemoryStorage()
		if bootstrap {
			if index <= 1 {
				e.stop("add-nodes: index must be > 1 when bootstrapping")
				return false
			}
			snap := &pb.Snapshot{Metadata: &pb.SnapshotMetadata{
				Index:     u64p(index),
				Term:      u64p(1),
				ConfState: &pb.ConfState{Voters: voters, Learners: learners},
			}}
			if st.ApplySnapshot(snap) != nil {
				e.stop("add-nodes: ApplySnapshot failed")
				return false
			}
		}
		mi := inflight
		if mi == 0 {
			mi = 1<<31 - 1 // upstream: math.MaxInt32
		}
		mcs := maxCommittedSize
		cfg := &raft.Config{
			ID:                          id,
			ElectionTick:                3, // upstream raftConfigStub
			HeartbeatTick:               1,
			Storage:                     st,
			Applied:                     index,
			MaxSizePerMsg:               ^uint64(0), // upstream: math.MaxUint64
			MaxCommittedSizePerReady:    mcs,
			MaxInflightMsgs:             mi,
			PreVote:                     prevote,
			CheckQuorum:                 checkquorum,
			StepDownOnRemoval:           stepDownOnRemoval,
			DisableConfChangeValidation: disableCCV,
			Logger:                      e.lg,
		}
		rn, err := raft.NewRawNode(cfg)
		if err != nil {
			e.stop("add-nodes: NewRawNode failed")
			return false
		}
		e.nodes = append(e.nodes, &envNode{rn: rn, st: st, applied: index})
	}
	return true
}

// processReady mirrors upstream ProcessReady exactly ONE Ready cycle:
// persist (HardState, then snapshot XOR entries), apply committed,
// route outbound messages to the bag, Advance.
func (e *renv) processReady(idx int) bool {
	nd := e.nodes[idx]
	rd := nd.rn.Ready()
	if !raft.IsEmptyHardState(rd.HardState) {
		if nd.st.SetHardState(rd.HardState) != nil {
			e.stop("SetHardState failed")
			return false
		}
		nd.term = rd.HardState.GetTerm()
		nd.commit = rd.HardState.GetCommit()
	}
	if !raft.IsEmptySnap(rd.Snapshot) {
		// The supported subset never compacts or sends snapshots; a
		// snapshot in Ready is outside it — fail closed, never approximate.
		e.stop("snapshot in Ready (outside the supported subset)")
		return false
	}
	if len(rd.Entries) > 0 {
		if nd.st.Append(rd.Entries) != nil {
			e.stop("Append failed")
			return false
		}
	}
	if rd.SoftState != nil {
		nd.state = rd.SoftState.RaftState
	}
	for _, ent := range rd.CommittedEntries {
		if ent.GetType() != pb.EntryNormal {
			// propose-conf-change is outside the supported subset, so a
			// conf-change entry cannot legitimately commit here.
			e.stop("non-normal committed entry (outside the supported subset)")
			return false
		}
		nd.applied = ent.GetIndex()
	}
	for _, m := range rd.Messages {
		e.msgs = append(e.msgs, m)
	}
	nd.rn.Advance(rd)
	return true
}

// deliverMsgs mirrors upstream DeliverMsgs/splitMsgs: for each recipient
// in the given order, remove ALL its bag messages (of type typ; -1 =
// all) in bag order and either step or drop them. Returns handled count.
func (e *renv) deliverMsgs(deliver []uint64, drop []uint64, typ int32) int {
	n := 0
	for _, id := range deliver {
		n += e.splitStep(id, typ, false)
	}
	for _, id := range drop {
		n += e.splitStep(id, typ, true)
	}
	return n
}

func (e *renv) splitStep(to uint64, typ int32, drop bool) int {
	var mine []*pb.Message
	var rest []*pb.Message
	for _, m := range e.msgs {
		if m.GetTo() == to && (typ < 0 || int32(m.GetType()) == typ) {
			mine = append(mine, m)
		} else {
			rest = append(rest, m)
		}
	}
	e.msgs = rest
	if drop {
		return len(mine)
	}
	for _, m := range mine {
		if int(to) > len(e.nodes) {
			e.stop("deliver to unknown node")
			return len(mine)
		}
		_ = e.nodes[to-1].rn.Step(m)
	}
	return len(mine)
}

// stabilize mirrors upstream Stabilize: fixed point of (a) ProcessReady
// on every listed node with HasReady, then (b) delivering every listed
// node's bag messages; empty list = all nodes.
func (e *renv) stabilize(idxs []int) bool {
	if len(idxs) == 0 {
		for i := range e.nodes {
			idxs = append(idxs, i)
		}
	}
	for round := 0; round < 10000; round++ {
		done := true
		for _, i := range idxs {
			if e.nodes[i].rn.HasReady() {
				if !e.processReady(i) {
					return false
				}
				done = false
			}
		}
		for _, i := range idxs {
			if e.splitStep(uint64(i+1), -1, false) > 0 {
				done = false
			}
			if e.halt {
				return false
			}
		}
		if done {
			return true
		}
	}
	e.stop("stabilize did not quiesce")
	return false
}

func (e *renv) campaign(idx int) bool {
	if e.nodes[idx].rn.Campaign() != nil {
		return false
	}
	return true
}

func (e *renv) propose(idx int, data string) bool {
	return e.nodes[idx].rn.Propose([]byte(data)) == nil
}

func (e *renv) tick(idx int, num int) {
	for i := 0; i < num; i++ {
		e.nodes[idx].rn.Tick()
	}
}

// block wraps one datadriven block: records the verdict + projection.
// ok=false renders "err" — for an upstream ok-expectation block that is
// a DISAGREEMENT tracereplay.py scores.
func (e *renv) block(k int, cmd string, ok bool) {
	v := " ok"
	if !ok {
		v = " err"
	}
	if e.halt {
		v = "" // the STOP note is already in the trace
	}
	e.say("b" + ritoa(k) + " " + cmd + v + e.projection() + "\n")
}
