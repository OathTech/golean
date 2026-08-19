// Copyright 2019 The etcd Authors
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

// OVERLAY (tools/raftsubject/overlay/raftpb/confchange.go) — a hand-written
// replacement for upstream raftpb/confchange.go, whose SHA-256 is pinned in
// tools/raftsubject/derive.py. Upstream is hand-written Go that imports the
// protobuf runtime, so it cannot be mechanically stripped.
//
// SUBJECT DELTA, itemised (docs/raft-w2-log.md, subject-delta ledger) — it is
// ONE change:
//
//  1. The `google.golang.org/protobuf/proto` import is gone, and with it
//     MarshalConfChange's two proto.Marshal calls: the body is now a
//     FAIL-CLOSED STUB that panics. This is the marshal-avoidance ruling
//     made executable — under the machine twin, membership is snapshot-seeded
//     and the only caller (node.go's confChangeToMsg) is not in the subject
//     tree, so the encode path is provably never taken. If it is ever taken,
//     a differential sees a panic, never a silent nil.
//
// Everything else in this file is upstream verbatim, INCLUDING the parts the
// frontend cannot lower today: EnterJoint's `panic(fmt.Sprintf(...))` and the
// strings/strconv rendering helpers stay exactly as etcd writes them, so they
// classify honestly in the refusal inventory rather than being papered over.

package raftpb

import (
	"fmt"
	"strconv"
	"strings"
)

// ConfChangeI abstracts over ConfChangeV2 and (legacy) ConfChange to allow
// treating them in a unified manner.
type ConfChangeI interface {
	// AsV2 should always return a non-nil object
	AsV2() *ConfChangeV2
	// AsV1 should always return a non-nil object
	AsV1() (*ConfChange, bool)
}

// MarshalConfChange calls Marshal on the underlying ConfChange or ConfChangeV2
// and returns the result along with the corresponding EntryType.
//
// FAIL-CLOSED STUB (subject delta 1). Upstream's body is two proto.Marshal
// calls; the plainpb shim has no encoder, by ruling. Under marshal-avoidance
// this is unreachable — membership is snapshot-seeded, so no ConfChange entry
// is ever encoded — and its only in-library caller (node.go confChangeToMsg)
// is outside the subject tree. Reaching it is a visible panic, not a nil.
func MarshalConfChange(c ConfChangeI) (EntryType, []byte, error) {
	panic("plainpb: MarshalConfChange is a fail-closed stub (marshal-avoidance ruling, docs/raft-w2-log.md)")
}

// AsV2 returns a V2 configuration change carrying out the same operation.
func (c *ConfChange) AsV2() *ConfChangeV2 {
	return &ConfChangeV2{
		Changes: []*ConfChangeSingle{{
			Type:   c.GetType().Enum(),
			NodeId: new(c.GetNodeId()),
		}},
		Context: c.Context,
	}
}

// AsV1 returns the ConfChange and true.
func (c *ConfChange) AsV1() (*ConfChange, bool) {
	return c, true
}

// AsV2 is the identity.
func (c *ConfChangeV2) AsV2() *ConfChangeV2 { return c }

// AsV1 returns nil and false.
func (c *ConfChangeV2) AsV1() (*ConfChange, bool) { return nil, false }

// EnterJoint returns two bools. The second bool is true if and only if this
// config change will use Joint Consensus, which is the case if it contains more
// than one change or if the use of Joint Consensus was requested explicitly.
// The first bool can only be true if second one is, and indicates whether the
// Joint State will be left automatically.
func (c *ConfChangeV2) EnterJoint() (autoLeave bool, ok bool) {
	// NB: in theory, more config changes could qualify for the "simple"
	// protocol but it depends on the config on top of which the changes apply.
	// For example, adding two learners is not OK if both nodes are part of the
	// base config (i.e. two voters are turned into learners in the process of
	// applying the conf change). In practice, these distinctions should not
	// matter, so we keep it simple and use Joint Consensus liberally.
	if c.GetTransition() != ConfChangeTransitionAuto || len(c.Changes) > 1 {
		// Use Joint Consensus.
		var autoLeave bool
		switch c.GetTransition() {
		case ConfChangeTransitionAuto:
			autoLeave = true
		case ConfChangeTransitionJointImplicit:
			autoLeave = true
		case ConfChangeTransitionJointExplicit:
		default:
			panic(fmt.Sprintf("unknown transition: %+v", c))
		}
		return autoLeave, true
	}
	return false, false
}

// LeaveJoint is true if the configuration change leaves a joint configuration.
// This is the case if the ConfChangeV2 is zero, with the possible exception of
// the Context field.
func (c *ConfChangeV2) LeaveJoint() bool {
	return c.GetTransition() == ConfChangeTransition_ConfChangeTransitionAuto &&
		len(c.GetChanges()) == 0
}

// ConfChangesFromString parses a Space-delimited sequence of operations into a
// slice of ConfChangeSingle. The supported operations are:
// - vn: make n a voter,
// - ln: make n a learner,
// - rn: remove n, and
// - un: update n.
func ConfChangesFromString(s string) ([]*ConfChangeSingle, error) {
	var ccs []*ConfChangeSingle
	toks := strings.Split(strings.TrimSpace(s), " ")
	if toks[0] == "" {
		toks = nil
	}
	for _, tok := range toks {
		if len(tok) < 2 {
			return nil, fmt.Errorf("unknown token %s", tok)
		}
		cc := &ConfChangeSingle{}
		switch tok[0] {
		case 'v':
			cc.Type = ConfChangeAddNode.Enum()
		case 'l':
			cc.Type = ConfChangeAddLearnerNode.Enum()
		case 'r':
			cc.Type = ConfChangeRemoveNode.Enum()
		case 'u':
			cc.Type = ConfChangeUpdateNode.Enum()
		default:
			return nil, fmt.Errorf("unknown input: %s", tok)
		}
		id, err := strconv.ParseUint(tok[1:], 10, 64)
		if err != nil {
			return nil, err
		}
		cc.NodeId = new(id)
		ccs = append(ccs, cc)
	}
	return ccs, nil
}

// ConfChangesToString is the inverse to ConfChangesFromString.
func ConfChangesToString(ccs []*ConfChangeSingle) string {
	var buf strings.Builder
	for i, cc := range ccs {
		if i > 0 {
			buf.WriteByte(' ')
		}
		switch cc.GetType() {
		case ConfChangeAddNode:
			buf.WriteByte('v')
		case ConfChangeAddLearnerNode:
			buf.WriteByte('l')
		case ConfChangeRemoveNode:
			buf.WriteByte('r')
		case ConfChangeUpdateNode:
			buf.WriteByte('u')
		default:
			buf.WriteString("unknown")
		}
		fmt.Fprintf(&buf, "%d", cc.GetNodeId())
	}
	return buf.String()
}
