// W4.2 item 1's POSITIVE probe — the other half of the dead-DYNAMICALLY
// census argument (docs/raft-w42-log.md item 1; pairs with
// logger-teeth-probe-main.go).
//
// The SAME single-node drive as W4.1's THE-MOMENT probe, but through the
// ruled logger seam: the harness installs ONE stateless logger value
// through BOTH seams — raft.SetLogger (covers the six getLogger() sites,
// three of them live in MemoryStorage) AND Config.Logger (covers every
// r.logger.* call) — BEFORE any node exists (§5 of the harness design;
// the Q2 ruling). A green machine run of this drive is a machine-checked
// witness that no DefaultLogger body was ever dispatched to: every one is
// a fail-closed stub that STOPS the machine when called (teeth witnessed
// by the paired probe).
//
// The drive also exercises the SetLogger seam POSITIVELY: a deliberate
// out-of-bound MemoryStorage.Entries call routes through
// getLogger().Panicf — under the installed logger that PANICS with a
// fixed string (raft's assertions keep their teeth), which the probe
// recovers and folds into the summary. Config.Logger alone would NOT
// catch this call (the getLogger() amendment, design §5) — so a summary
// with the teeth digit set is evidence the registry seam is the one that
// fired.
//
// Expected on both oracles: 1111035
//   (teeth=1)*1000000 + the W4.1 111035 drive summary
//   (isLeader=1, term=1, committedNormal=1, applied=3, rounds=5).
//
// Run: tools/raftsubject/runprobe.py --main logger-installed-probe-main.go \
//        --function probeLoggerInstalled
package main

import (
	"raft"
	pb "raftpb"
)

func u64(v uint64) *uint64 { return &v }

// harnessLogger is the HARNESS-OWNED Logger (design §5): eight empty
// bodies (the informational levels — nothing is rendered, so no fmt path
// runs) and four that panic with fixed strings (Fatal/Fatalf/Panic/Panicf
// — "stop the machine" is the honest reading of both; there is no
// os.Exit to model). It is STATELESS — no fields, so every method reads
// and writes nothing, its footprint is empty, and sharing ONE value
// across all n nodes cannot appear in any pairwise-disjointness
// obligation of the §6 shared-nothing reduction argument. A logger that
// buffered output would be shared mutable state on every node's every
// event and would silently invalidate that argument; if a recording
// logger is ever needed it must be per node, and §6's footprint check
// re-run.
type harnessLogger struct{}

func (l *harnessLogger) Debug(v ...any)                   {}
func (l *harnessLogger) Debugf(format string, v ...any)   {}
func (l *harnessLogger) Info(v ...any)                    {}
func (l *harnessLogger) Infof(format string, v ...any)    {}
func (l *harnessLogger) Warning(v ...any)                 {}
func (l *harnessLogger) Warningf(format string, v ...any) {}
func (l *harnessLogger) Error(v ...any)                   {}
func (l *harnessLogger) Errorf(format string, v ...any)   {}
func (l *harnessLogger) Fatal(v ...any) {
	panic("raftharness: Logger.Fatal")
}
func (l *harnessLogger) Fatalf(format string, v ...any) {
	panic("raftharness: Logger.Fatalf")
}
func (l *harnessLogger) Panic(v ...any) {
	panic("raftharness: Logger.Panic")
}
func (l *harnessLogger) Panicf(format string, v ...any) {
	panic("raftharness: Logger.Panicf")
}

// registryTeeth provokes the SetLogger seam: MemoryStorage.Entries with
// hi out of bound routes through getLogger().Panicf (storage.go:154 —
// one of the three live getLogger() sites Config.Logger cannot reach).
// Returns 1 iff the installed logger's panic fired and was recovered.
func registryTeeth(st *raft.MemoryStorage) (teeth int) {
	defer func() {
		if recover() != nil {
			teeth = 1
		}
	}()
	_, _ = st.Entries(2, 99, 1<<20) // lastIndex is 1: hi is out of bound
	return 0
}

func probeLoggerInstalled() int {
	// THE CONSTRUCTOR ORDER IS THE ARGUMENT: both seams are supplied
	// before any node (or storage use) exists, and never again.
	lg := &harnessLogger{}
	raft.SetLogger(lg) // seam 1: the package registry (six getLogger() sites)

	st := raft.NewMemoryStorage()
	if st.ApplySnapshot(&pb.Snapshot{Metadata: &pb.SnapshotMetadata{
		Index:     u64(1),
		Term:      u64(1),
		ConfState: &pb.ConfState{Voters: []uint64{1}},
	}}) != nil {
		return -1
	}

	teeth := registryTeeth(st)

	cfg := &raft.Config{
		ID:              1,
		ElectionTick:    10,
		HeartbeatTick:   1,
		Storage:         st,
		MaxSizePerMsg:   1 << 20,
		MaxInflightMsgs: 256,
		Logger:          lg, // seam 2: the per-node seam (every r.logger.* call)
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
	return teeth*1000000 + isLeader*100000 + termCapped*10000 +
		committedNormal*1000 + appliedCapped*10 + rounds
}

func main() {
	println(probeLoggerInstalled())
}
