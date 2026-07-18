package main

// Edge probes for the quorum threshold q = n/2 + 1 at the smallest configs,
// where off-by-one errors in the threshold hide. n=1 (q=1) and n=2 (q=2).
// 2=won, 1=pending, 0=lost.

type majoritySet map[uint64]struct{}

func (c majoritySet) voteResult(votes map[uint64]bool) int {
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

func set(ids ...uint64) majoritySet {
	m := majoritySet{}
	for _, id := range ids {
		m[id] = struct{}{}
	}
	return m
}

func voteN1Won() int     { return set(1).voteResult(map[uint64]bool{1: true}) }
func voteN1Lost() int    { return set(1).voteResult(map[uint64]bool{1: false}) }
func voteN1Pending() int { return set(1).voteResult(map[uint64]bool{}) }
func voteN2Won() int     { return set(1, 2).voteResult(map[uint64]bool{1: true, 2: true}) }
func voteN2OneYesLost() int      { return set(1, 2).voteResult(map[uint64]bool{1: true, 2: false}) }
func voteN2OneMissingPending() int { return set(1, 2).voteResult(map[uint64]bool{1: true}) }
