// Package mnode: the mini-raft node state machine (W4.3 item 4). A
// deliberately SMALL consensus core with raft's language shape: state
// enum, per-term votes, an appended log, quorum commit, applied
// tracking. NOT etcd raft — the twin instrument
// (tools/raftsubject/twin-lib.go) drives the real subject; this family
// pins the COMPOSITION SHAPE in the gated corpus (multi-package
// structs/interfaces/maps/slices under a schedule-driven driver).
package mnode

import "mpb"

type State int

const (
	Follower State = iota
	Candidate
	Leader
)

func (s State) Char() string {
	switch s {
	case Candidate:
		return "C"
	case Leader:
		return "L"
	}
	return "F"
}

type Node struct {
	ID      uint64
	N       int
	Term    uint64
	Vote    uint64 // 0 = none
	State   State
	Log     []mpb.Entry
	Commit  uint64
	Applied []string // applied data, in order

	votes map[uint64]bool // grants received this term (candidate)
	acks  map[uint64]uint64
}

func New(id uint64, n int) *Node {
	return &Node{ID: id, N: n, votes: map[uint64]bool{}, acks: map[uint64]uint64{}}
}

func (nd *Node) quorum() int { return nd.N/2 + 1 }

func (nd *Node) becomeFollower(term uint64) {
	nd.State = Follower
	if term > nd.Term {
		nd.Term = term
		nd.Vote = 0
	}
	nd.votes = map[uint64]bool{}
}

// Campaign starts an election (the explicit-campaign vocabulary — no
// timers, no jitter: schedules drive elections, as upstream's
// datadriven `campaign` command does).
func (nd *Node) Campaign() []*mpb.Message {
	nd.State = Candidate
	nd.Term++
	nd.Vote = nd.ID
	nd.votes = map[uint64]bool{nd.ID: true}
	out := []*mpb.Message{}
	for id := uint64(1); id <= uint64(nd.N); id++ {
		if id == nd.ID {
			continue
		}
		out = append(out, &mpb.Message{Type: mpb.MsgVote, From: nd.ID, To: id,
			Term: nd.Term, Index: uint64(len(nd.Log))})
	}
	if len(nd.votes) >= nd.quorum() { // n=1
		nd.State = Leader
	}
	return out
}

// Propose appends a command on a leader; a non-leader drops it
// (the drop-and-retry client, harness design §3).
func (nd *Node) Propose(data string) ([]*mpb.Message, bool) {
	if nd.State != Leader {
		return nil, false
	}
	nd.Log = append(nd.Log, mpb.Entry{Term: nd.Term, Data: data})
	nd.acks[nd.ID] = uint64(len(nd.Log))
	out := []*mpb.Message{}
	for id := uint64(1); id <= uint64(nd.N); id++ {
		if id == nd.ID {
			continue
		}
		out = append(out, &mpb.Message{Type: mpb.MsgApp, From: nd.ID, To: id,
			Term: nd.Term, Index: uint64(len(nd.Log) - 1),
			Entries: []mpb.Entry{nd.Log[len(nd.Log)-1]}, Commit: nd.Commit})
	}
	return out, true
}

// Step consumes one delivered message and returns the responses.
func (nd *Node) Step(m *mpb.Message) []*mpb.Message {
	if m.Term > nd.Term {
		nd.becomeFollower(m.Term)
	}
	out := []*mpb.Message{}
	switch m.Type {
	case mpb.MsgVote:
		granted := m.Term >= nd.Term && (nd.Vote == 0 || nd.Vote == m.From) &&
			m.Index >= uint64(len(nd.Log))
		if granted {
			nd.Vote = m.From
		}
		out = append(out, &mpb.Message{Type: mpb.MsgVoteResp, From: nd.ID,
			To: m.From, Term: nd.Term, Granted: granted})
	case mpb.MsgVoteResp:
		if nd.State == Candidate && m.Term == nd.Term && m.Granted {
			nd.votes[m.From] = true
			if len(nd.votes) >= nd.quorum() {
				nd.State = Leader
				nd.acks = map[uint64]uint64{nd.ID: uint64(len(nd.Log))}
			}
		}
	case mpb.MsgApp:
		if m.Term < nd.Term {
			break
		}
		nd.State = Follower
		// Mini contract: entries arrive in order; a gap is refused by
		// acking the current length (the leader here never has gaps in
		// the drain schedules; a starved node simply lags).
		if m.Index == uint64(len(nd.Log)) {
			nd.Log = append(nd.Log, m.Entries...)
		}
		if m.Commit > nd.Commit && m.Commit <= uint64(len(nd.Log)) {
			nd.Commit = m.Commit
		}
		// The AppResp carries the follower's COMMIT so the leader's
		// commit-update stops at parity (without it the update loop
		// ping-pongs to the drain cap — witnessed as interpreter
		// minutes before this line existed; docs/raft-w43-log.md).
		out = append(out, &mpb.Message{Type: mpb.MsgAppResp, From: nd.ID,
			To: m.From, Term: nd.Term, Index: uint64(len(nd.Log)),
			Commit: nd.Commit})
	case mpb.MsgAppResp:
		if nd.State == Leader && m.Term == nd.Term {
			if m.Index > nd.acks[m.From] {
				nd.acks[m.From] = m.Index
			}
			nd.maybeCommit()
			if nd.Commit > m.Commit {
				out = append(out, &mpb.Message{Type: mpb.MsgApp, From: nd.ID,
					To: m.From, Term: nd.Term, Index: uint64(len(nd.Log)),
					Commit: nd.Commit})
			}
		}
	}
	// Apply everything committed (the harvest-bundled apply).
	for uint64(len(nd.Applied)) < nd.Commit {
		nd.Applied = append(nd.Applied, nd.Log[len(nd.Applied)].Data)
	}
	return out
}

// maybeCommit advances Commit to the highest index acked by a quorum
// (current-term entries only — raft's own commit rule, miniaturized).
func (nd *Node) maybeCommit() {
	for idx := nd.Commit + 1; idx <= uint64(len(nd.Log)); idx++ {
		cnt := 0
		for id := uint64(1); id <= uint64(nd.N); id++ {
			if nd.acks[id] >= idx {
				cnt++
			}
		}
		if cnt >= nd.quorum() && nd.Log[idx-1].Term == nd.Term {
			nd.Commit = idx
		}
	}
	for uint64(len(nd.Applied)) < nd.Commit {
		nd.Applied = append(nd.Applied, nd.Log[len(nd.Applied)].Data)
	}
}
