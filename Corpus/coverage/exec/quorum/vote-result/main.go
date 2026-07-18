package main

// A faithful reduction of quorum.MajorityConfig.VoteResult exercising the
// decision boundary that carries the quorum safety property. Outcomes are
// encoded 2=won, 1=pending, 0=lost. Every subject is order-insensitive.

type majoritySet map[uint64]struct{}

func (c majoritySet) voteResult(votes map[uint64]bool) int {
	if len(c) == 0 {
		// By convention the election on an empty config wins.
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

func voteSet(ids ...uint64) majoritySet {
	m := majoritySet{}
	for _, id := range ids {
		m[id] = struct{}{}
	}
	return m
}

// Empty config wins by convention.
func voteResultEmptyWins() int {
	return voteSet().voteResult(map[uint64]bool{})
}

// Odd config, yes exactly reaches quorum (q=2 of 3).
func voteResultWonExact() int {
	return voteSet(1, 2, 3).voteResult(map[uint64]bool{1: true, 2: true, 3: false})
}

// Odd config, no votes reach quorum.
func voteResultLost() int {
	return voteSet(1, 2, 3).voteResult(map[uint64]bool{1: false, 2: false, 3: false})
}

// Odd config, outcome still depends on missing voters.
func voteResultPending() int {
	return voteSet(1, 2, 3).voteResult(map[uint64]bool{1: true})
}

// Even config, quorum is n/2+1 = 3, reached exactly.
func voteResultEvenWon() int {
	return voteSet(1, 2, 3, 4).voteResult(map[uint64]bool{1: true, 2: true, 3: true, 4: false})
}

// Even config, one short of the even-n quorum threshold.
func voteResultEvenOneShort() int {
	return voteSet(1, 2, 3, 4).voteResult(map[uint64]bool{1: true, 2: true, 3: false, 4: false})
}

// Two-voter tie loses: quorum is 2, only one yes.
func voteResultTieLost() int {
	return voteSet(1, 2).voteResult(map[uint64]bool{1: true, 2: false})
}
