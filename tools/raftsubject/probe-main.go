// W2 frontier probe: the tracked subject tree (raftsubject/) verbatim, with a
// harness-shaped main. Measures what refuses NOW, with plainpb + the no-op
// logger in place. PROBE ARTIFACT — not the subject tree itself.
package main

import (
	"quorum"
	"raft"
	pb "raftpb"
	"tracker"
)

func probeTracker() int {
	p := tracker.Progress{Match: 3, Next: 4}
	return int(p.Match + p.Next)
}

func probeCommitted() int {
	c := quorum.MajorityConfig{1: {}, 2: {}, 3: {}}
	l := mapAckIndexer{1: 8, 2: 5, 3: 3}
	return int(c.CommittedIndex(l))
}

type mapAckIndexer map[uint64]quorum.Index

func (m mapAckIndexer) AckedIndex(id uint64) (quorum.Index, bool) {
	idx, ok := m[id]
	return idx, ok
}

// probeConfState drives the plainpb real-logic path: ProgressTracker.ConfState
// builds a *pb.ConfState, and Equivalent compares two of them.
func probeConfState() int {
	a := &pb.ConfState{Voters: []uint64{3, 1, 2}}
	b := &pb.ConfState{Voters: []uint64{1, 2, 3}}
	if a.Equivalent(b) == nil {
		return 1
	}
	return 0
}

func main() {
	raft.ResetDefaultLogger()
	println(probeTracker(), probeCommitted(), probeConfState())
}
