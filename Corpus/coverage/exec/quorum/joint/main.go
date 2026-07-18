package main

// A faithful reduction of quorum.JointConfig ([2]MajorityConfig): a defined
// array type over a defined map type, with array indexing (c[0]/c[1]), range
// over the defined array (in ids), and the joint combination rules for
// VoteResult (both must agree; either lost => lost; else pending) and
// CommittedIndex (min of the two halves). Vote outcomes: 2=won, 1=pending,
// 0=lost. All subjects are order-insensitive.

const maxUint64 = ^uint64(0)

type majorityConfig map[uint64]struct{}

func (c majorityConfig) voteResult(votes map[uint64]bool) int {
	if len(c) == 0 {
		return 2
	}
	yes, missing := 0, 0
	for id := range c {
		v, ok := votes[id]
		if !ok {
			missing++
			continue
		}
		if v {
			yes++
		}
	}
	q := len(c)/2 + 1
	if yes >= q {
		return 2
	}
	if yes+missing >= q {
		return 1
	}
	return 0
}

func (c majorityConfig) committedIndex(acks map[uint64]uint64) uint64 {
	n := len(c)
	if n == 0 {
		return maxUint64
	}
	srt := make([]uint64, n)
	i := n - 1
	for id := range c {
		if idx, ok := acks[id]; ok {
			srt[i] = idx
			i--
		}
	}
	for a := 1; a < len(srt); a++ {
		for b := a; b > 0 && srt[b-1] > srt[b]; b-- {
			srt[b-1], srt[b] = srt[b], srt[b-1]
		}
	}
	pos := n - (n/2 + 1)
	return srt[pos]
}

type jointConfig [2]majorityConfig

func (c jointConfig) voteResult(votes map[uint64]bool) int {
	r1 := c[0].voteResult(votes)
	r2 := c[1].voteResult(votes)
	if r1 == r2 {
		return r1
	}
	if r1 == 0 || r2 == 0 {
		return 0
	}
	return 1
}

func (c jointConfig) committedIndex(acks map[uint64]uint64) uint64 {
	i0 := c[0].committedIndex(acks)
	i1 := c[1].committedIndex(acks)
	if i0 < i1 {
		return i0
	}
	return i1
}

func (c jointConfig) ids() map[uint64]struct{} {
	m := map[uint64]struct{}{}
	for _, cc := range c {
		for id := range cc {
			m[id] = struct{}{}
		}
	}
	return m
}

func mc(ids ...uint64) majorityConfig {
	m := majorityConfig{}
	for _, id := range ids {
		m[id] = struct{}{}
	}
	return m
}

// Both halves win: agreement returns won.
func jointVoteBothWin() int {
	votes := map[uint64]bool{1: true, 2: true, 3: true, 4: true, 5: true}
	return jointConfig{mc(1, 2, 3), mc(3, 4, 5)}.voteResult(votes)
}

// One half wins, the other loses: loss dominates.
func jointVoteDisagreeLost() int {
	votes := map[uint64]bool{1: true, 2: true, 3: true, 4: false, 5: false}
	return jointConfig{mc(1, 2, 3), mc(4, 5)}.voteResult(votes)
}

// One half wins, the other is pending: outcome is pending.
func jointVoteDisagreePending() int {
	votes := map[uint64]bool{1: true, 2: true, 3: true, 4: true}
	return jointConfig{mc(1, 2, 3), mc(4, 5, 6)}.voteResult(votes)
}

// Both halves pending: agreement returns pending.
func jointVoteBothPending() int {
	return jointConfig{mc(1, 2, 3), mc(4, 5, 6)}.voteResult(map[uint64]bool{1: true, 4: true})
}

// Committed index is the min of the two halves' committed indexes.
func jointCommittedMin() int {
	acks := map[uint64]uint64{1: 10, 2: 20, 3: 30, 4: 5, 5: 15}
	return int(jointConfig{mc(1, 2, 3), mc(3, 4, 5)}.committedIndex(acks))
}

// IDs is the set union across the two halves (nested range over the array).
func jointIDsUnion() int {
	return len(jointConfig{mc(1, 2, 3), mc(3, 4)}.ids())
}
