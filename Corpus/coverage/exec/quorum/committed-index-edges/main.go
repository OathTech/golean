package main

// Edge probes for CommittedIndex at n=1 and with unacked voters, where the
// zero-fill-on-the-left and single-element median cases hide.

const maxUint64 = ^uint64(0)

type voterSet map[uint64]struct{}

func (c voterSet) committedIndex(acks map[uint64]uint64) uint64 {
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
	return srt[n-(n/2+1)]
}

func vset(ids ...uint64) voterSet {
	m := voterSet{}
	for _, id := range ids {
		m[id] = struct{}{}
	}
	return m
}

// Single voter, acked: committed index is that voter's index.
func committedN1Acked() int { return int(vset(1).committedIndex(map[uint64]uint64{1: 99})) }

// Single voter, unacked: the zero slot is the committed index.
func committedN1Unacked() int { return int(vset(1).committedIndex(map[uint64]uint64{})) }

// All voters unacked: the median of all-zero slots is zero.
func committedAllUnacked() int { return int(vset(1, 2, 3).committedIndex(map[uint64]uint64{})) }
