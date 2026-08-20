// W4.1's THE-MOMENT probe: the first RawNode execution through the
// machine (docs/raft-w41-log.md, the post-census step). A minimal
// SINGLE-NODE RawNode drive — snapshot-seeded membership, a tick, a
// campaign, a propose, Ready harvests with Advance — run under BOTH
// `go run` and the machine by tools/raftsubject/runprobe.py, comparing
// the summary observation. PROBE ARTIFACT — not the subject tree, not
// the W4.2 twin (no network, no checker, n=1); its only claim is
// "the RawNode path RUNS and the two oracles agree on this drive".
package main

import (
	"raft"
	pb "raftpb"
)

func u64(v uint64) *uint64 { return &v }

// probeRawNode returns a digit-packed summary of the drive:
//   isLeader*100000 + termCapped*10000 + committedNormal*1000 +
//   appliedCapped*10 + readyRounds
// where isLeader comes from the LAST harvested SoftState (the twin's
// S1 claim source), term from the last harvested HardState,
// committedNormal counts committed EntryNormal entries with non-empty
// data (the proposal), applied is the highest committed index seen,
// and readyRounds counts harvests (capped at 9 for stable packing).
func probeRawNode() int {
	st := raft.NewMemoryStorage()
	err := st.ApplySnapshot(&pb.Snapshot{Metadata: &pb.SnapshotMetadata{
		Index:     u64(1),
		Term:      u64(1),
		ConfState: &pb.ConfState{Voters: []uint64{1}},
	}})
	if err != nil {
		return -1
	}
	cfg := &raft.Config{
		ID:              1,
		ElectionTick:    10,
		HeartbeatTick:   1,
		Storage:         st,
		MaxSizePerMsg:   1 << 20,
		MaxInflightMsgs: 256,
	}
	rn, err := raft.NewRawNode(cfg)
	if err != nil {
		return -2
	}

	rounds := 0
	committedNormal := 0
	applied := uint64(0)
	term := uint64(0)
	isLeader := 0
	fail := 0

	harvest := func() {
		for rn.HasReady() && rounds < 9 {
			rd := rn.Ready()
			rounds++
			if rd.SoftState != nil {
				if rd.SoftState.RaftState == raft.StateLeader {
					isLeader = 1
				} else {
					isLeader = 0
				}
			}
			if !raft.IsEmptyHardState(rd.HardState) {
				term = rd.HardState.GetTerm()
				if st.SetHardState(rd.HardState) != nil {
					fail = -100
					return
				}
			}
			if len(rd.Entries) > 0 {
				if st.Append(rd.Entries) != nil {
					fail = -200
					return
				}
			}
			for _, e := range rd.CommittedEntries {
				if e.GetType() == pb.EntryNormal && len(e.GetData()) > 0 {
					committedNormal++
				}
				if e.GetIndex() > applied {
					applied = e.GetIndex()
				}
			}
			rn.Advance(rd)
		}
	}

	rn.Tick()
	if rn.Campaign() != nil {
		return -3
	}
	harvest()
	if fail != 0 {
		return fail
	}
	if rn.Propose([]byte("x")) != nil {
		return -4
	}
	harvest()
	if fail != 0 {
		return fail
	}

	termCapped := int(term)
	if termCapped > 9 {
		termCapped = 9
	}
	appliedCapped := int(applied)
	if appliedCapped > 9 {
		appliedCapped = 9
	}
	return isLeader*100000 + termCapped*10000 + committedNormal*1000 + appliedCapped*10 + rounds
}

func main() {
	println(probeRawNode())
}
