package main

// THE QUORUM PILOT SUBJECT (phase 3, docs/2026-07-30_quorum-pilot-arc.md):
// the REAL etcd-io/raft CommittedIndex, vendored VERBATIM — see README.md
// for the recorded delta. Drivers below are etcd's own
// testdata/majority_commit.txt rows.

import (
	"math"
	"slices"
)

// ---- quorum.go (verbatim subset) ----

// Index is a Raft log position.
type Index uint64

// AckedIndexer allows looking up a commit index for a given ID of a voter
// from a corresponding MajorityConfig.
type AckedIndexer interface {
	AckedIndex(voterID uint64) (idx Index, found bool)
}

type mapAckIndexer map[uint64]Index

func (m mapAckIndexer) AckedIndex(id uint64) (Index, bool) {
	idx, ok := m[id]
	return idx, ok
}

// ---- majority.go (verbatim subset) ----

// MajorityConfig is a set of IDs that uses majority quorums to make decisions.
type MajorityConfig map[uint64]struct{}

// Slice returns the MajorityConfig as a sorted slice.
func (c MajorityConfig) Slice() []uint64 {
	var sl []uint64
	for id := range c {
		sl = append(sl, id)
	}
	slices.Sort(sl)
	return sl
}

// CommittedIndex computes the committed index from those supplied via the
// provided AckedIndexer (for the active config).
func (c MajorityConfig) CommittedIndex(l AckedIndexer) Index {
	n := len(c)
	if n == 0 {
		// This plays well with joint quorums which, when one half is the zero
		// MajorityConfig, should behave like the other half.
		return math.MaxUint64
	}

	// Use an on-stack slice to collect the committed indexes when n <= 7
	// (otherwise we alloc). The alternative is to stash a slice on
	// MajorityConfig, but this impairs usability (as is, MajorityConfig is just
	// a map, and that's nice). The assumption is that running with a
	// replication factor of >7 is rare, and in cases in which it happens
	// performance is a lesser concern (additionally the performance
	// implications of an allocation here are far from drastic).
	var stk [7]uint64
	var srt []uint64
	if len(stk) >= n {
		srt = stk[:n]
	} else {
		srt = make([]uint64, n)
	}

	{
		// Fill the slice with the indexes observed. Any unused slots will be
		// left as zero; these correspond to voters that may report in, but
		// haven't yet. We fill from the right (since the zeroes will end up on
		// the left after sorting below anyway).
		i := n - 1
		for id := range c {
			if idx, ok := l.AckedIndex(id); ok {
				srt[i] = uint64(idx)
				i--
			}
		}
	}
	slices.Sort(srt)

	// The smallest index into the array for which the value is acked by a
	// quorum. In other words, from the end of the slice, move n/2+1 to the
	// left (accounting for zero-indexing).
	pos := n - (n/2 + 1)
	return Index(srt[pos])
}

// ---- drivers: etcd's testdata/majority_commit.txt rows ----

func run(c MajorityConfig, l mapAckIndexer) uint64 {
	return uint64(c.CommittedIndex(l))
}

func committedEmpty() uint64 {
	return run(MajorityConfig{}, mapAckIndexer{})
}

func committedOneMissing() uint64 {
	return run(MajorityConfig{1: {}}, mapAckIndexer{})
}

func committedOneKnown() uint64 {
	return run(MajorityConfig{1: {}}, mapAckIndexer{1: 12})
}

func committedTwoMissing() uint64 {
	return run(MajorityConfig{1: {}, 2: {}}, mapAckIndexer{})
}

func committedTwoHalf() uint64 {
	return run(MajorityConfig{1: {}, 2: {}}, mapAckIndexer{1: 12})
}

func committedTwoKnown() uint64 {
	return run(MajorityConfig{1: {}, 2: {}}, mapAckIndexer{1: 12, 2: 5})
}

func committedThreeMissing() uint64 {
	return run(MajorityConfig{1: {}, 2: {}, 3: {}}, mapAckIndexer{})
}

func committedThreeOne() uint64 {
	return run(MajorityConfig{1: {}, 2: {}, 3: {}}, mapAckIndexer{1: 12})
}

func committedThreeTwo() uint64 {
	return run(MajorityConfig{1: {}, 2: {}, 3: {}}, mapAckIndexer{1: 12, 2: 5})
}

func committedThreeAll() uint64 {
	return run(MajorityConfig{1: {}, 2: {}, 3: {}}, mapAckIndexer{1: 12, 2: 5, 3: 6})
}

func committedThreeAllLow() uint64 {
	return run(MajorityConfig{1: {}, 2: {}, 3: {}}, mapAckIndexer{1: 12, 2: 5, 3: 4})
}

func committedThreeDupTwo() uint64 {
	return run(MajorityConfig{1: {}, 2: {}, 3: {}}, mapAckIndexer{1: 5, 2: 5})
}

func committedThreeDupAll() uint64 {
	return run(MajorityConfig{1: {}, 2: {}, 3: {}}, mapAckIndexer{1: 5, 2: 5, 3: 12})
}

func committedThreeSpread() uint64 {
	return run(MajorityConfig{1: {}, 2: {}, 3: {}}, mapAckIndexer{1: 100, 2: 101, 3: 103})
}

func committedFiveDup() uint64 {
	return run(MajorityConfig{1: {}, 2: {}, 3: {}, 4: {}, 5: {}},
		mapAckIndexer{1: 101, 2: 104, 3: 103, 4: 103})
}

func committedFiveSpread() uint64 {
	return run(MajorityConfig{1: {}, 2: {}, 3: {}, 4: {}, 5: {}},
		mapAckIndexer{1: 101, 2: 102, 3: 103, 4: 103})
}

func sortedSlice() uint64 {
	sl := MajorityConfig{3: {}, 1: {}, 2: {}}.Slice()
	return sl[0]*100 + sl[1]*10 + sl[2]
}
