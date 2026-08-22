// The datadriven-trace REPLAY ENV, v2 — the RENDERED tier (W4.3 items
// 2+3; docs/raft-w43-log.md), superseding the W4.2 ok-tier-only mirror
// (docs/raft-w42-log.md item 3).
//
// A faithful plain-Go mirror of deps/raft/rafttest's InteractionEnv +
// RedirectLogger for the SUPPORTED command subset, including the OUTPUT
// each handler renders: per block, this env produces the same string
// upstream's Handle() returns ("ok" iff the output buffer is empty),
// which tracereplay.py compares against the trace file's expected text —
// the one oracle in this instrument family EXTERNAL to us (the
// tier-strength bound, docs/raft-w42-log.md item 4: the ok tier is blind
// to delivery order and the machine/byte tier is oracle-symmetric; THIS
// comparison is what can falsify the mirror).
//
// v2 changes against the W4.2 mirror, each argued at its site:
//   - the RECORDING logger (the W4.2 structural finding): a mirror of
//     upstream's RedirectLogger — level-gated log lines rendered into
//     the same buffer the handlers write. REPLAY-ENV-ONLY, never the
//     twin's: the twin's logger stays stateless by the §5/§6
//     shared-nothing argument; this env is sequential measurement
//     tooling and makes no reduction claim (recorded as JC-30).
//   - deliver-msgs takes upstream's ONE ordered recipient list with a
//     per-recipient Drop flag — latent mirror divergence #2 (W4.2
//     pre-merge audit) closed SOURCE-VERBATIM, UNEXERCISED BY EVERY
//     TIER (audit R2-F2 relabeled this from "RETIRING": mutation
//     M4 — drops reordered before delivers — leaves the full go-side
//     suite green at 206/206 ok + 148/148 rendered, re-verified
//     2026-08-22, so the mirroring is the whole argument; no trace
//     mixes drop and deliver recipients in one command).
//   - splitMsgs carries upstream's `!(drop && isLocalMsg(msg))` guard —
//     latent mirror divergence #1 (same audit) closed SOURCE-VERBATIM,
//     UNEXERCISED BY EVERY TIER (same relabeling; mutation M3 —
//     guard removed — leaves the suite green at the same numbers: no
//     supported trace has a local message in the bag at a drop).
//   - conf-change support (propose-conf-change + the apply path's
//     ApplyConfChange dispatch), unblocking the 11 traces whose stop
//     was "multi-line command input".
//   - process-ready/stabilize render DescribeReady, the "> N handling
//     Ready"/"> N receiving messages" headers and the two-space indent
//     (withIndent), exactly as upstream.
//
// Still outside the subset, fail closed (reasons in tracereplay.py's
// docstring): compact/send-snapshot (the env implements no handlers
// for the two COMMANDS — audit R2-F1 corrected this line, whose first
// version said "no History bookkeeping" and listed snapshots-in-Ready
// as outside: BACKWARDS on both counts, since v2 KEEPS History (the
// appender state machine above) and APPLIES snapshots from Ready —
// that is exactly what makes conf-change snapshot catch-up work),
// async storage writes,
// tick-election/set-randomized-election-timeout (jitter),
// transfer-leadership/forget-leader/report-unreachable,
// add-nodes content=/read-only/async-storage-writes args.
//
// This file is package-main LIBRARY source: tracereplay.py copies it
// beside a GENERATED main.go (the parsed command sequence of one trace)
// into a scratch program. It compiles only together with such a main.
package main

import (
	"fmt"

	"proto"
	"raft"
	pb "raftpb"
	"tracker"
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

// ---- the recording logger (JC-30) --------------------------------------
//
// Mirrors rafttest's RedirectLogger over the env's output buffer: level
// names, the level gate on print/printf, the trailing-newline rule, and
// the NONE-suppresses-everything Write override. Upstream embeds
// *strings.Builder and hands ITSELF to every node's Config.Logger; this
// mirror does the same through the env pointer.

var lvlNames = [...]string{"DEBUG", "INFO", "WARN", "ERROR", "FATAL", "NONE"}

type renv struct {
	nodes []*envNode
	msgs  []*pb.Message // the in-flight message bag, insertion-ordered
	lvl   int           // 0=DEBUG .. 5=NONE (RedirectLogger.Lvl)
	buf   []byte        // the per-block output buffer (RedirectLogger.Builder)
	trace string        // the accumulated whole-trace observation
	halt  bool          // a fail-closed replay stop (recorded, ends the run)
}

type envNode struct {
	rn *raft.RawNode
	st *raft.MemoryStorage

	// history mirrors upstream rafttest's Node.History: the appender
	// state machine's snapshots, one per applied entry, seeded with the
	// bootstrap snapshot. LIVE in conf-change traces: the leader sends
	// the newly added node a snapshot whose content is History's last
	// (the snapOverrideStorage below), so it is not compact-only
	// bookkeeping.
	history []*pb.Snapshot

	// harness-observed projection state (same sourcing as the twin's).
	term    uint64
	commit  uint64
	state   raft.StateType
	applied uint64
}

// snapOverrideStorage mirrors upstream rafttest's: raft.Storage backed
// by the node's MemoryStorage, except Snapshot() returns the most
// recent History snapshot (deferred through the env, as upstream's
// closure defers through env.Nodes).
type snapOverrideStorage struct {
	*raft.MemoryStorage
	e   *renv
	idx int
}

func (s snapOverrideStorage) Snapshot() (*pb.Snapshot, error) {
	h := s.e.nodes[s.idx].history
	return h[len(h)-1], nil
}

func newEnv() *renv {
	e := &renv{}
	raft.SetLogger(e)
	return e
}

func (e *renv) quiet() bool { return e.lvl == 5 }

// out is the RedirectLogger Write-override mirror: handler AND log
// writes both land here, and NONE suppresses both.
func (e *renv) out(s string) {
	if e.quiet() {
		return
	}
	e.buf = append(e.buf, s...)
}

func (e *renv) printfLvl(lvl int, format string, v []any) {
	if e.lvl <= lvl {
		e.out(lvlNames[lvl] + " ")
		s := fmt.Sprintf(format, v...)
		e.out(s)
		if n := len(format); n > 0 && format[n-1] != '\n' {
			e.out("\n")
		}
	}
}

func (e *renv) printLvl(lvl int, v []any) {
	if e.lvl <= lvl {
		e.out(lvlNames[lvl] + " ")
		e.out(fmt.Sprintln(v...))
	}
}

func (e *renv) Debug(v ...any)                   { e.printLvl(0, v) }
func (e *renv) Debugf(format string, v ...any)   { e.printfLvl(0, format, v) }
func (e *renv) Info(v ...any)                    { e.printLvl(1, v) }
func (e *renv) Infof(format string, v ...any)    { e.printfLvl(1, format, v) }
func (e *renv) Warning(v ...any)                 { e.printLvl(2, v) }
func (e *renv) Warningf(format string, v ...any) { e.printfLvl(2, format, v) }
func (e *renv) Error(v ...any)                   { e.printLvl(3, v) }
func (e *renv) Errorf(format string, v ...any)   { e.printfLvl(3, format, v) }

// Fatal/Panic mirror RedirectLogger: log at FATAL, then panic — the
// stop-the-machine reading; upstream panics with the formatted string.
func (e *renv) Fatal(v ...any) {
	e.printLvl(4, v)
	panic(fmt.Sprint(v...))
}
func (e *renv) Fatalf(format string, v ...any) {
	e.printfLvl(4, format, v)
	panic(fmt.Sprintf(format, v...))
}
func (e *renv) Panic(v ...any) {
	e.printLvl(4, v)
	panic(fmt.Sprint(v...))
}
func (e *renv) Panicf(format string, v ...any) {
	e.printfLvl(4, format, v)
	panic(fmt.Sprintf(format, v...))
}

// setLogLevel mirrors LogLevel's strings.EqualFold match (the level
// names are ASCII, so an ASCII fold is exact).
func (e *renv) setLogLevel(name string) bool {
	up := make([]byte, len(name))
	for i := 0; i < len(name); i++ {
		c := name[i]
		if c >= 'a' && c <= 'z' {
			c -= 'a' - 'A'
		}
		up[i] = c
	}
	for i := 0; i < len(lvlNames); i++ {
		if lvlNames[i] == string(up) {
			e.lvl = i
			return true
		}
	}
	return false
}

// withIndent mirrors InteractionEnv.withIndent: run f with a fresh
// buffer, then append every produced line under a two-space indent.
func (e *renv) withIndent(f func()) {
	orig := e.buf
	e.buf = nil
	f()
	inner := e.buf
	e.buf = orig
	// bufio.Scanner semantics: split on '\n', drop a trailing empty
	// final token, strip a trailing '\r' per line.
	start := 0
	for i := 0; i <= len(inner); i++ {
		if i == len(inner) {
			if start < i {
				e.out("  " + string(inner[start:i]) + "\n")
			}
			break
		}
		if inner[i] == '\n' {
			line := inner[start:i]
			if n := len(line); n > 0 && line[n-1] == '\r' {
				line = line[:n-1]
			}
			e.out("  " + string(line) + "\n")
			start = i + 1
		}
	}
}

func (e *renv) stop(why string) {
	e.halt = true
	e.out(" STOP:" + why)
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
	s := "|"
	for _, nd := range e.nodes {
		s += stChar(nd.state) + rutoa(nd.term) + "/" + rutoa(nd.commit) +
			"/" + rutoa(nd.applied) + " "
	}
	return s + "bag=" + ritoa(len(e.msgs))
}

// ---- handlers -----------------------------------------------------------

// addNodes mirrors upstream AddNodes + raftConfigStub: n fresh nodes,
// ids continuing the sequence, snapshot-seeded iff voters/learners/index
// given (upstream requires index > 1 then, and stamps Metadata.Term=1).
// History IS kept (the appender state machine); compact/send-snapshot
// stay outside because their COMMAND handlers are unimplemented
// (audit R2-F1 — the first version of this line claimed "no History
// bookkeeping", contradicting the history field 170 lines up).
func (e *renv) addNodes(n int, voters []uint64, learners []uint64, index uint64,
	prevote bool, checkquorum bool, inflight int, maxCommittedSize uint64,
	stepDownOnRemoval bool, disableCCV bool) error {
	// ONE snapshot value, shared by all n nodes' storages and History
	// seeds — upstream builds it once in handleAddNodes and reuses it.
	snap := pb.EnsureSnapshot(&pb.Snapshot{Metadata: &pb.SnapshotMetadata{
		Index:     u64p(index),
		ConfState: &pb.ConfState{Voters: voters, Learners: learners},
	}})
	bootstrap := len(voters) > 0 || len(learners) > 0 || index > 0
	for i := 0; i < n; i++ {
		id := uint64(1 + len(e.nodes))
		st := raft.NewMemoryStorage()
		if bootstrap {
			if index <= 1 {
				return errString("index must be specified as > 1 due to bootstrap")
			}
			snap.Metadata.Term = u64p(1) // upstream stamps Term=1
			if err := st.ApplySnapshot(snap); err != nil {
				return err
			}
		}
		// inflight < 0 means the arg was ABSENT (audit R2-F3: the old
		// encoding used 0 for absent, making an EXPLICIT `inflight=0`
		// indistinguishable from no arg — upstream would Scan the 0
		// into MaxInflightMsgs and the config would reject it, where
		// this mirror silently substituted MaxInt32).
		mi := inflight
		if mi < 0 {
			mi = 1<<31 - 1 // upstream default: math.MaxInt32
		}
		nd := &envNode{st: st, history: []*pb.Snapshot{snap}, applied: index}
		e.nodes = append(e.nodes, nd)
		cfg := &raft.Config{
			ID:                          id,
			ElectionTick:                3, // upstream raftConfigStub
			HeartbeatTick:               1,
			Storage:                     snapOverrideStorage{MemoryStorage: st, e: e, idx: int(id) - 1},
			Applied:                     index,
			MaxSizePerMsg:               ^uint64(0), // upstream: math.MaxUint64
			MaxCommittedSizePerReady:    maxCommittedSize,
			MaxInflightMsgs:             mi,
			PreVote:                     prevote,
			CheckQuorum:                 checkquorum,
			StepDownOnRemoval:           stepDownOnRemoval,
			DisableConfChangeValidation: disableCCV,
			Logger:                      e, // the recording logger (JC-30)
		}
		rn, err := raft.NewRawNode(cfg)
		if err != nil {
			e.nodes = e.nodes[:len(e.nodes)-1]
			return err
		}
		nd.rn = rn
	}
	return nil
}

type stringErr string

func (s stringErr) Error() string { return string(s) }

func errString(s string) error { return stringErr(s) }

// processReady mirrors upstream ProcessReady exactly ONE Ready cycle:
// render DescribeReady, persist (HardState, then snapshot XOR entries),
// apply committed (conf changes included), route outbound messages to
// the bag, Advance.
func (e *renv) processReady(idx int) error {
	nd := e.nodes[idx]
	rd := nd.rn.Ready()
	e.out(raft.DescribeReady(rd, defaultEntryFormatter))
	// processAppend mirror: HardState, then snapshot XOR entries.
	if !raft.IsEmptyHardState(rd.HardState) {
		if err := nd.st.SetHardState(rd.HardState); err != nil {
			return err
		}
		nd.term = rd.HardState.GetTerm()
		nd.commit = rd.HardState.GetCommit()
	}
	if !raft.IsEmptySnap(rd.Snapshot) {
		if len(rd.Entries) > 0 {
			return errString("can't apply snapshot and entries at the same time")
		}
		if err := nd.st.ApplySnapshot(rd.Snapshot); err != nil {
			return err
		}
		nd.applied = rd.Snapshot.GetMetadata().GetIndex() // projection only
	} else if len(rd.Entries) > 0 {
		if err := nd.st.Append(rd.Entries); err != nil {
			return err
		}
	}
	if rd.SoftState != nil {
		nd.state = rd.SoftState.RaftState
	}
	// processApply mirror, conf-change dispatch + the appender state
	// machine's History bookkeeping (upstream processApply verbatim,
	// minus the protobuf-runtime Unmarshal spelling).
	for _, ent := range rd.CommittedEntries {
		var update []byte
		var cs *pb.ConfState
		switch ent.GetType() {
		case pb.EntryConfChange:
			cc := &pb.ConfChange{}
			if err := proto.Unmarshal(ent.GetData(), cc); err != nil {
				return err
			}
			update = cc.Context
			cs = nd.rn.ApplyConfChange(cc)
		case pb.EntryConfChangeV2:
			cc := &pb.ConfChangeV2{}
			if err := proto.Unmarshal(ent.GetData(), cc); err != nil {
				return err
			}
			cs = nd.rn.ApplyConfChange(cc)
			update = cc.Context
		default:
			update = ent.GetData()
		}
		lastSnap := nd.history[len(nd.history)-1]
		snap := pb.EnsureSnapshot(nil)
		snap.Data = append(snap.Data, lastSnap.Data...)
		// NB (upstream): this hard-codes an "appender" state machine.
		snap.Data = append(snap.Data, update...)
		snap.Metadata.Index = u64p(ent.GetIndex())
		snap.Metadata.Term = u64p(ent.GetTerm())
		if cs == nil {
			cs = lastSnap.GetMetadata().GetConfState()
		}
		snap.Metadata.ConfState = cs
		nd.history = append(nd.history, snap)
		nd.applied = ent.GetIndex() // projection only
	}
	for _, m := range rd.Messages {
		if raft.IsLocalMsgTarget(m.GetTo()) {
			// AsyncStorageWrites is never set in the supported subset;
			// upstream panics here in that mode.
			e.stop("local msg target (async storage writes outside the subset)")
			return nil
		}
		e.msgs = append(e.msgs, m)
	}
	nd.rn.Advance(rd)
	return nil
}

// handleProcessReady mirrors the handler: multi-node form prints the
// "> N handling Ready" header and indents.
func (e *renv) handleProcessReady(idxs []int) error {
	for _, idx := range idxs {
		var err error
		if len(idxs) > 1 {
			e.out("> " + ritoa(idx+1) + " handling Ready\n")
			e.withIndent(func() { err = e.processReady(idx) })
		} else {
			err = e.processReady(idx)
		}
		if err != nil {
			return err
		}
	}
	return nil
}

func defaultEntryFormatter(b []byte) string { return fmt.Sprintf("%q", b) }

// isLocalMsg mirrors rafttest's: local messages require reliable
// delivery and are never dropped.
func isLocalMsg(m *pb.Message) bool {
	return m.GetFrom() == m.GetTo() || raft.IsLocalMsgTarget(m.GetFrom()) ||
		raft.IsLocalMsgTarget(m.GetTo())
}

// splitMsgs mirrors rafttest's splitMsgs verbatim, including the
// don't-drop-local guard (divergence #1: source-verbatim, unexercised
// by every tier — mutation M3 stays green; see the header note).
func (e *renv) splitMsgs(to uint64, typ int32, drop bool) []*pb.Message {
	var mine []*pb.Message
	var rest []*pb.Message
	for _, m := range e.msgs {
		if m.GetTo() == to && !(drop && isLocalMsg(m)) &&
			(typ < 0 || int32(m.GetType()) == typ) {
			mine = append(mine, m)
		} else {
			rest = append(rest, m)
		}
	}
	e.msgs = rest
	return mine
}

// peekMsgs reports whether any bag message addresses `to` (the
// stabilize header probe), WITHOUT mutating the bag — upstream calls
// splitMsgs on env.Messages and discards the remainder.
func (e *renv) peekMsgs(to uint64) bool {
	for _, m := range e.msgs {
		if m.GetTo() == to {
			return true
		}
	}
	return false
}

// recipient mirrors rafttest.Recipient.
type recipient struct {
	id   uint64
	drop bool
}

// deliverMsgs mirrors upstream DeliverMsgs over ONE ordered recipient
// list (divergence #2: source-verbatim, unexercised by every tier —
// mutation M4 stays green; see the header note): per recipient in
// argument order, remove
// its bag messages and deliver or drop, rendering each DescribeMessage
// line ("dropped: " prefix on drops). Returns handled count.
func (e *renv) deliverMsgs(rs []recipient, typ int32) int {
	n := 0
	for _, r := range rs {
		msgs := e.splitMsgs(r.id, typ, r.drop)
		n += len(msgs)
		for _, m := range msgs {
			if r.drop {
				e.out("dropped: ")
			}
			e.out(raft.DescribeMessage(m, defaultEntryFormatter) + "\n")
			if r.drop {
				continue
			}
			if int(m.GetTo()) > len(e.nodes) {
				e.stop("deliver to unknown node")
				return n
			}
			if err := e.nodes[m.GetTo()-1].rn.Step(m); err != nil {
				e.out(err.Error() + "\n")
			}
		}
	}
	return n
}

func (e *renv) handleDeliverMsgs(rs []recipient, typ int32) {
	if n := e.deliverMsgs(rs, typ); n == 0 {
		e.out("no messages\n")
	}
}

// stabilize mirrors upstream Stabilize: fixed point of (a) ProcessReady
// (with header+indent) on every listed node with HasReady, then (b)
// delivering every listed node's bag messages (with header+indent);
// empty list = all nodes. The append/apply-thread arms are outside the
// subset (AsyncStorageWrites never set).
func (e *renv) stabilize(idxs []int) error {
	if len(idxs) == 0 {
		for i := range e.nodes {
			idxs = append(idxs, i)
		}
	}
	for round := 0; round < 10000; round++ {
		done := true
		for _, i := range idxs {
			if e.nodes[i].rn.HasReady() {
				e.out("> " + ritoa(i+1) + " handling Ready\n")
				var err error
				e.withIndent(func() { err = e.processReady(i) })
				if err != nil {
					return err
				}
				done = false
			}
		}
		for _, i := range idxs {
			id := uint64(i + 1)
			// NB (upstream): peek just to see whether to print the
			// header; DeliverMsgs does the real split.
			if e.peekMsgs(id) {
				e.out("> " + rutoa(id) + " receiving messages\n")
				e.withIndent(func() { e.deliverMsgs([]recipient{{id: id}}, -1) })
				done = false
			}
			if e.halt {
				return nil
			}
		}
		if done {
			return nil
		}
	}
	e.stop("stabilize did not quiesce")
	return nil
}

// stabilizeWithLogLevel mirrors handleStabilize's log-level override:
// the level is set for the stabilize and restored after.
func (e *renv) stabilizeWithLogLevel(idxs []int, lvlName string) error {
	old := e.lvl
	if !e.setLogLevel(lvlName) {
		return errString("log levels must be either of [DEBUG INFO WARN ERROR FATAL NONE]")
	}
	err := e.stabilize(idxs)
	e.lvl = old
	return err
}

func (e *renv) campaign(idx int) error {
	return e.nodes[idx].rn.Campaign()
}

func (e *renv) propose(idx int, data string) error {
	return e.nodes[idx].rn.Propose([]byte(data))
}

// proposeConfChange mirrors handleProposeConfChange: parse the change
// string with the subject's own ConfChangesFromString, build the v1 or
// v2 message, propose it.
func (e *renv) proposeConfChange(idx int, ccString string, v1 bool, transition pb.ConfChangeTransition) error {
	ccs, err := pb.ConfChangesFromString(ccString)
	if err != nil {
		return err
	}
	var c pb.ConfChangeI
	if v1 {
		if len(ccs) > 1 || transition != pb.ConfChangeTransition_ConfChangeTransitionAuto {
			return errString("v1 conf change can only have one operation and no transition")
		}
		c = &pb.ConfChange{
			Type:   ccs[0].GetType().Enum(),
			NodeId: new(ccs[0].GetNodeId()),
		}
	} else {
		c = &pb.ConfChangeV2{
			Transition: transition.Enum(),
			Changes:    ccs,
		}
	}
	return e.nodes[idx].rn.ProposeConfChange(c)
}

func (e *renv) tick(idx int, num int) {
	for i := 0; i < num; i++ {
		e.nodes[idx].rn.Tick()
	}
}

// handleRaftState mirrors the handler: per node, from its OWN status.
func (e *renv) handleRaftState() {
	for _, nd := range e.nodes {
		st := nd.rn.Status()
		voterStatus := "(Non-Voter)"
		idMap := st.Config.Voters.IDs()
		for idx := range idMap {
			if st.ID == idx {
				voterStatus = "(Voter)"
			}
		}
		e.out(fmt.Sprintf("%d: %s %s Term:%d Lead:%d\n",
			st.ID, st.RaftState, voterStatus, st.GetTerm(), st.Lead))
	}
}

// handleStatus mirrors the handler: the node's Progress map printed via
// ProgressMap.String (upstream routes it through fmt.Fprint, which
// calls the same String).
func (e *renv) handleStatus(idx int) {
	st := e.nodes[idx].rn.Status()
	m := tracker.ProgressMap{}
	for id, pr := range st.Progress {
		pr := pr // loop-local copy (upstream's)
		m[id] = &pr
	}
	e.out(m.String())
}

// handleRaftLog mirrors the handler.
func (e *renv) handleRaftLog(idx int) error {
	s := e.nodes[idx].st
	fi, err := s.FirstIndex()
	if err != nil {
		return err
	}
	li, err := s.LastIndex()
	if err != nil {
		return err
	}
	if li < fi {
		e.out(fmt.Sprintf("log is empty: first index=%d, last index=%d", fi, li))
		return nil
	}
	ents, err := s.Entries(fi, li+1, ^uint64(0))
	if err != nil {
		return err
	}
	e.out(raft.DescribeEntries(ents, defaultEntryFormatter))
	return nil
}

// block wraps one datadriven block: run the handler body, then record
// the block's rendered output exactly as upstream's Handle returns it —
// err.Error() appended to the buffer (or returned alone under quiet),
// "ok" iff the buffer is empty. The trace stream carries unambiguous
// markers for tracereplay.py plus the projection (extra signal for the
// oracle-symmetric byte tier; upstream has no counterpart, so it rides
// OUTSIDE the block-output segment).
func (e *renv) block(k int, cmd string, err error) {
	if err != nil && !e.quiet() {
		e.out(err.Error())
	}
	outStr := string(e.buf)
	if err != nil && e.quiet() {
		outStr = err.Error()
	}
	if outStr == "" {
		outStr = "ok"
	}
	if len(outStr) == 0 || outStr[len(outStr)-1] != '\n' {
		outStr += "\n"
	}
	e.trace += "\x01B " + ritoa(k) + " " + cmd + "\n" + outStr +
		"\x01E " + ritoa(k) + " " + e.projection() + "\n"
	e.buf = nil
}
