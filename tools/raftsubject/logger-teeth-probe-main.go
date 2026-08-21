// W4.2 item 1's NEGATIVE probe — the checkable half of the
// dead-DYNAMICALLY census argument (docs/raft-w42-log.md item 1).
//
// The tree carries upstream logger.go VERBATIM (D-5 retired), so the ten
// DefaultLogger formatting methods are fail-closed quarantined stubs. The
// census reports five of them STATICALLY live (interface dispatch is
// over-approximated). The dynamic argument is: the harness installs its
// own Logger through BOTH seams before any node exists, so DefaultLogger
// is never the dispatch target. This probe witnesses the CONTRAPOSITIVE:
// a drive that does NOT install a logger stops the machine at
// DefaultLogger.Infof the moment newRaft logs — i.e. the stub has teeth,
// so a green run of the same drive WITH the harness logger installed
// (logger-installed-probe-main.go, and the twin itself) is a meaningful
// machine-checked negative, not a vacuous one.
//
// Run: tools/raftsubject/runprobe.py --main logger-teeth-probe-main.go \
//        --function probeLoggerTeeth --expect-stop DefaultLogger.Infof
//
// Under `go run` the same drive dies loudly too — DefaultLogger's embedded
// *log.Logger is nil under the recorded D-12 initializer patch, so the
// first Output call nil-derefs. Loud on both oracles, silent on neither.
package main

import (
	"raft"
	pb "raftpb"
)

func u64(v uint64) *uint64 { return &v }

func probeLoggerTeeth() int {
	st := raft.NewMemoryStorage()
	if st.ApplySnapshot(&pb.Snapshot{Metadata: &pb.SnapshotMetadata{
		Index:     u64(1),
		Term:      u64(1),
		ConfState: &pb.ConfState{Voters: []uint64{1}},
	}}) != nil {
		return -1
	}
	cfg := &raft.Config{
		ID:              1,
		ElectionTick:    10,
		HeartbeatTick:   1,
		Storage:         st,
		MaxSizePerMsg:   1 << 20,
		MaxInflightMsgs: 256,
		// NO Logger, and NO raft.SetLogger: Config.validate falls back to
		// getLogger() = defaultLogger = &DefaultLogger{}, and newRaft's
		// unconditional r.logger.Infof is the first dynamic dispatch into
		// the quarantined stub family.
	}
	rn, err := raft.NewRawNode(cfg)
	if err != nil {
		return -2
	}
	_ = rn
	return 0 // never reached on either oracle
}

func main() {
	println(probeLoggerTeeth())
}
