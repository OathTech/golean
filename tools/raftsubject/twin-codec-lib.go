// THE ROUTE A CODEC SCHEDULES THROUGH RAWNODE (route A slice S2;
// docs/2026-10-04_route-a-protobuf-design.md D9 + §5 «Through RawNode»;
// [USER] Mike 2026-10-05 «Go ahead with Route A S2», relayed).
//
// Two hand schedules over the machine-twin harness (twin-lib.go: the
// n=3 cluster, the message multiset, the stateless harness Logger), run
// under BOTH `go run` and the machine by runprobe.py. INSTRUMENTS, not
// gates. Each proposes a hand-encoded ConfChange ENTRY — raw bytes, not
// a ProposeConfChange (which would encode a well-formed value) — at the
// FOLLOWER node 2, so the proposal travels the multiset as a forwarded
// MsgProp and is decoded where raft decodes it: the leader's stepLeader
// (raft/raft.go:1326, `proto.Unmarshal(e.GetData(), ccc)` →
// `panic(err)` on failure).
//
//   - codec-abort (twin-codec-abort-main.go): the payload is a
//     well-formed ConfChange followed by a group START tag for field 15
//     (0x7b) and nothing else — a group left open at end of input, which
//     protobuf-go v1.36.11 refuses (`protowire.ConsumeFieldValue` →
//     errCodeTruncated → `errDecode`, impl/decode.go:218-224). The
//     leader's decode fails and raft panics with the error VALUE: the
//     program ABORTS with `proto: cannot parse invalid wire-format data`,
//     the prefix being EITHER spelling (U+0020 or U+00A0 — the subject
//     proto's ONE init-time `rand.Intn(2)` pick, D5/Q1). runprobe.py
//     checks MEMBERSHIP over the two texts on both legs
//     (`--expect-panic-member`, twice).
//   - codec-unknown-group (twin-codec-group-main.go): the same
//     ConfChange followed by a COMPLETE unknown group for field 15
//     carrying one nested varint field (0x7b 0x08 0x2a 0x7c) — which
//     protobuf-go accepts and RETAINS as unknown bytes (U-2/U-3). The
//     leader accepts the proposal, the entry reaches Ready (the leader's
//     rd.Entries, payload byte-identical) and commits on all three
//     nodes; each node's application decodes it through the subject
//     `proto`, applies it (ConfChangeUpdateNode for node 2: a
//     configuration no-op, so the cluster shape is unchanged and no
//     message is addressed outside the twin), and re-encodes it — the
//     re-encoding equals the proposed bytes (the group retained and
//     re-emitted after the known fields). The observation is the trace.
//
// twin-lib.go's own harvest treats every non-EntryNormal entry as an
// S3 anomaly («v1 proposes no conf changes»); this file therefore runs
// its OWN harvest (harvestCC: twin-lib's harvest with a conf-change
// apply arm, every other step identical) and leaves twin-lib.go — and
// with it the pinned twin wire (baselines/pins/twin-chdriver.wire.json)
// — untouched.
package main

import (
	"proto"
	"raft"
	pb "raftpb"
)

// ccPayload: the proposed ConfChange (UpdateNode, node 2, id 7)
// encoded by the subject's own Marshal, then `tail` appended verbatim.
func ccPayload(tail []byte) []byte {
	cc := &pb.ConfChange{
		Type:   pb.ConfChangeUpdateNode.Enum(),
		NodeId: u64(2),
		Id:     u64(7),
	}
	b, err := proto.Marshal(cc)
	if err != nil {
		return nil
	}
	out := []byte{}
	for i := 0; i < len(b); i++ {
		out = append(out, b[i])
	}
	for i := 0; i < len(tail); i++ {
		out = append(out, tail[i])
	}
	return out
}

func hexBytes(b []byte) string {
	const digits = "0123456789abcdef"
	s := ""
	for i := 0; i < len(b); i++ {
		s += string(digits[b[i]>>4]) + string(digits[b[i]&15])
	}
	return s
}

func sameBytes(x, y []byte) bool {
	if len(x) != len(y) {
		return false
	}
	for i := 0; i < len(x); i++ {
		if x[i] != y[i] {
			return false
		}
	}
	return true
}

// proposeRawCC: the raw ConfChange entry proposed at node `id`
// (RawNode.Step with a MsgProp, the shape RawNode.Propose builds, the
// entry typed EntryConfChange).
func (t *twin) proposeRawCC(id int, data []byte) {
	nd := t.nodes[id-1]
	t.say("proposeCC" + itoa(id) + "=" + hexBytes(data))
	err := nd.rn.Step(&pb.Message{
		Type: pb.MsgProp.Enum(),
		From: u64(uint64(id)),
		Entries: []*pb.Entry{{
			Type: pb.EntryConfChange.Enum(),
			Data: data,
		}},
	})
	if err != nil {
		t.say(" dropped")
	}
	t.harvestCC(nd, data)
}

// harvestCC: twin-lib.go's harvest (persist before send, record,
// send, apply, Advance — to LOCAL quiescence) with one extra arm: a
// committed EntryConfChange is decoded through the subject proto,
// applied, and re-encoded, and the leader-side Ready that first
// carries the proposed payload is traced.
func (t *twin) harvestCC(nd *twinNode, want []byte) int {
	rounds := 0
	for nd.rn.HasReady() {
		rounds++
		if rounds > 64 {
			t.halt = true
			t.viol("harness: harvest did not quiesce in 64 rounds")
			return rounds
		}
		rd := nd.rn.Ready()
		if !raft.IsEmptyHardState(rd.HardState) {
			if nd.st.SetHardState(rd.HardState) != nil {
				t.halt = true
				t.viol("harness: SetHardState failed")
				return rounds
			}
			nd.term = rd.HardState.GetTerm()
			nd.commit = rd.HardState.GetCommit()
		}
		for _, e := range rd.Entries {
			if e.GetType() == pb.EntryConfChange {
				same := 0
				if sameBytes(e.GetData(), want) {
					same = 1
				}
				t.say(" ready" + utoa(nd.id) + ":cc@" + utoa(e.GetIndex()) + " same=" + itoa(same))
			}
		}
		if len(rd.Entries) > 0 {
			if nd.st.Append(rd.Entries) != nil {
				t.halt = true
				t.viol("harness: Append failed")
				return rounds
			}
		}
		if !raft.IsEmptySnap(rd.Snapshot) {
			t.halt = true
			t.viol("harness: unexpected snapshot")
			return rounds
		}
		if rd.SoftState != nil {
			nd.state = rd.SoftState.RaftState
			if rd.SoftState.RaftState == raft.StateLeader {
				t.claims++
				prev, ok := t.leaderOf[nd.term]
				if ok && prev != nd.id {
					t.viol("S1 election safety: term " + utoa(nd.term) +
						" claimed by both node " + utoa(prev) +
						" and node " + utoa(nd.id))
				}
				t.leaderOf[nd.term] = nd.id
			}
		}
		for _, m := range rd.Messages {
			t.net = append(t.net, m)
			t.live = append(t.live, true)
		}
		for _, e := range rd.CommittedEntries {
			if e.GetType() == pb.EntryConfChange {
				t.applyCC(nd, e, want)
			} else {
				t.apply(nd, e)
			}
		}
		nd.rn.Advance(rd)
	}
	return rounds
}

// applyCC: the application's conf-change arm — decode (subject proto),
// ApplyConfChange, re-encode; S3's index/term monotonicity kept.
func (t *twin) applyCC(nd *twinNode, e *pb.Entry, want []byte) {
	idx := e.GetIndex()
	trm := e.GetTerm()
	if idx <= nd.applied {
		t.viol("S3 monotonicity: node " + utoa(nd.id) + " applied index " +
			utoa(idx) + " after index " + utoa(nd.applied))
	}
	if trm < nd.lastTrm {
		t.viol("S3 monotonicity: node " + utoa(nd.id) + " applied term " +
			utoa(trm) + " after term " + utoa(nd.lastTrm))
	}
	nd.applied = idx
	nd.lastTrm = trm
	cc := &pb.ConfChange{}
	if err := proto.Unmarshal(e.GetData(), cc); err != nil {
		t.viol("apply: node " + utoa(nd.id) + " cannot decode the committed conf change: " + err.Error())
		return
	}
	cs := nd.rn.ApplyConfChange(cc)
	re, err := proto.Marshal(cc)
	if err != nil {
		t.viol("apply: node " + utoa(nd.id) + " cannot re-encode the conf change")
		return
	}
	reSame := 0
	if sameBytes(re, want) {
		reSame = 1
	}
	t.say(" apply" + utoa(nd.id) + ":cc@" + utoa(idx) + " type=" + itoa(int(cc.GetType())) +
		" node=" + utoa(cc.GetNodeId()) + " voters=" + itoa(len(cs.GetVoters())) +
		" size=" + itoa(proto.Size(cc)) + " reencode-same=" + itoa(reSame))
}

func (t *twin) deliverCC(i int, want []byte) {
	m := t.net[i]
	t.live[i] = false
	to := t.nodes[m.GetTo()-1]
	if err := to.rn.Step(m); err != nil {
		t.say(" steperr")
	}
	t.harvestCC(to, want)
}

// drainCC: twin-lib's opDrain (insertion order, to quiescence) over
// harvestCC.
func (t *twin) drainCC(want []byte) {
	t.say("drain")
	for n := 0; n < 10000; n++ {
		i := -1
		for j := range t.net {
			if t.live[j] {
				i = j
				break
			}
		}
		if i < 0 {
			return
		}
		t.deliverCC(i, want)
	}
	t.halt = true
	t.viol("harness: drain did not quiesce")
}

// runCodecSched: elect node 1 (campaign + drain), propose the raw
// payload at follower 2, drain. The projection follows each event, as
// in runSched.
func runCodecSched(name string, data []byte) string {
	installLogger()
	t := newTwin(3, 0)
	t.say("[" + name + "]\n")
	if t.halt {
		return t.trace
	}
	t.say("e1 campaign1")
	if t.nodes[0].rn.Campaign() != nil {
		t.say(" err")
	}
	t.harvestCC(t.nodes[0], data)
	t.say(t.projection() + "\ne2 ")
	t.drainCC(data)
	t.say(t.projection() + "\ne3 ")
	t.proposeRawCC(2, data)
	t.say(t.projection() + "\ne4 ")
	t.drainCC(data)
	t.say(t.projection() + "\n")
	t.say("end viol=" + itoa(t.violations) + " claims=" + itoa(t.claims) + "\n")
	return t.trace
}

// probeTwinCodecAbort: the malformed proposal (a group left open at
// end of input). Expected: the leader's decode panics with errDecode on
// both oracles — the function never returns.
func probeTwinCodecAbort() string {
	return runCodecSched("codec-abort", ccPayload([]byte{0x7b}))
}

// probeTwinCodecUnknownGroup: the proposal with a complete unknown
// group (field 15, one nested varint field 1 = 42). Expected: accepted,
// committed and applied on all three nodes, re-encoded byte-identical.
func probeTwinCodecUnknownGroup() string {
	return runCodecSched("codec-unknown-group", ccPayload([]byte{0x7b, 0x08, 0x2a, 0x7c}))
}
