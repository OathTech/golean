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

// OVERLAY (tools/raftsubject/overlay/raftpb/confstate.go) — a hand-written
// replacement for upstream raftpb/confstate.go, whose SHA-256 is pinned in
// tools/raftsubject/derive.py. Upstream cannot be mechanically stripped: it
// is hand-written Go that calls into the protobuf runtime (proto.Clone,
// proto.Equal) and formats its mismatch error with fmt.
//
// SUBJECT DELTA, itemised (docs/raft-w2-log.md, subject-delta ledger):
//
//  1. proto.Clone(cs).(*ConfState)  ->  cs.CloneMessage()
//     proto.Equal(cs1v, cs2v)       ->  cs1v.EqualMessage(cs2v)
//     Same operation, plain Go, no reflection. The generated
//     CloneMessage/EqualMessage carry the differential obligation against
//     the upstream pair (raft-w2 log, "differential obligations").
//
//  2. The mismatch error's TEXT loses the four %+#v value dumps. The
//     VERDICT — nil vs non-nil error — is unchanged, and raft's callers
//     (confchange restore checks, rawnode) branch on the verdict only; they
//     never inspect the string. Losing the dumps is what keeps `fmt` out of
//     raftpb, which is the whole point of the no-op-logger / quarantine lane.
//     The nil-input error likewise becomes a fixed-text sentinel.
//
//  3. `slices.Sort` is kept: it is the one modeled stdlib extern
//     (docs/2026-07-30_quorum-extern-policy.md), already exercised by
//     quorum.MajorityConfig.CommittedIndex.
//
// Everything else — the sorting, the nil-AutoLeave-is-false normalisation,
// the operate-on-copies discipline, and the comparison itself — is upstream's
// algorithm, transcribed.

package raftpb

import "slices"

// confStateError is the fixed-text error type this overlay returns in place
// of upstream's fmt.Errorf values (delta 2 above).
type confStateError string

func (e confStateError) Error() string { return string(e) }

// ErrConfStateNilInput is returned by Equivalent when either input is nil.
const ErrConfStateNilInput = confStateError("cannot compare ConfState: nil input")

// ErrConfStateNotEquivalent is returned by Equivalent when the two
// configurations differ after sorting.
const ErrConfStateNotEquivalent = confStateError("ConfStates not equivalent after sorting")

// Equivalent returns a nil error if the inputs describe the same configuration.
// On mismatch, returns a descriptive error showing the differences.
func (cs *ConfState) Equivalent(cs2 *ConfState) error {
	if cs == nil || cs2 == nil {
		return ErrConfStateNilInput
	}

	cs1v := cs.CloneMessage()
	cs2v := cs2.CloneMessage()

	s := func(sl *[]uint64) {
		slices.Sort(*sl)
	}
	for _, c := range []*ConfState{cs1v, cs2v} {
		s(&c.Voters)
		s(&c.Learners)
		s(&c.VotersOutgoing)
		s(&c.LearnersNext)

		// Treat nil AutoLeave as false.
		autoLeave := c.GetAutoLeave()
		c.AutoLeave = &autoLeave
	}

	if !cs1v.EqualMessage(cs2v) {
		return ErrConfStateNotEquivalent
	}
	return nil
}
