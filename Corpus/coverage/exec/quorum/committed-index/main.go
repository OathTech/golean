package main

// A reduction of quorum.MajorityConfig.CommittedIndex: the on-stack-else-heap
// slice selection, right-to-left fill of acked indexes, sort, and median pick
// that computes the committed index. The real code uses slices.Sort; this uses
// a hand-rolled insertion sort so the case is pure Go until the slices.Sort
// extern lands (a slices.Sort-faithful variant is added then). Subjects are
// order-insensitive: the fill order varies with map iteration but the result
// is taken after sorting.

const maxUint64 = ^uint64(0)

type voterSet map[uint64]struct{}

func (c voterSet) committedIndex(acks map[uint64]uint64) uint64 {
	n := len(c)
	if n == 0 {
		// Empty config behaves like the other half of a joint quorum.
		return maxUint64
	}
	var stk [7]uint64
	var srt []uint64
	if len(stk) >= n {
		srt = stk[:n]
	} else {
		srt = make([]uint64, n)
	}
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

func voterSetOf(ids ...uint64) voterSet {
	m := voterSet{}
	for _, id := range ids {
		m[id] = struct{}{}
	}
	return m
}

// Empty config yields the MaxUint64 convention (also exercises uint64 max in
// the observation pipeline).
func committedIndexEmpty() uint64 {
	return voterSetOf().committedIndex(map[uint64]uint64{})
}

// All voters acked, odd config: committed index is the median.
func committedIndexAllAcked() uint64 {
	return voterSetOf(1, 2, 3).committedIndex(map[uint64]uint64{1: 10, 2: 20, 3: 30})
}

// One voter has not acked: its zero slot drags the median down.
func committedIndexUnacked() uint64 {
	return voterSetOf(1, 2, 3).committedIndex(map[uint64]uint64{1: 10, 2: 20})
}

// Seven voters: the on-stack array branch (len(stk) >= n).
func committedIndexOnStack() uint64 {
	return voterSetOf(1, 2, 3, 4, 5, 6, 7).committedIndex(
		map[uint64]uint64{1: 10, 2: 20, 3: 30, 4: 40, 5: 50, 6: 60, 7: 70})
}

// Eight voters: the heap make branch (n > 7).
func committedIndexHeap() uint64 {
	return voterSetOf(1, 2, 3, 4, 5, 6, 7, 8).committedIndex(
		map[uint64]uint64{1: 10, 2: 20, 3: 30, 4: 40, 5: 50, 6: 60, 7: 70, 8: 80})
}
