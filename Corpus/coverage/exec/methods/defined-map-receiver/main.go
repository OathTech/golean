package main

import "fmt"

// majoritySet is a defined type whose underlying type is a map. Methods on
// non-struct defined receivers are quorum's central idiom (MajorityConfig).
type majoritySet map[uint64]struct{}

// voteCount is a faithful reduction of quorum.MajorityConfig.VoteResult:
// order-insensitive tally over map membership with comma-ok lookup and
// len-based quorum arithmetic. 2 = won, 1 = pending, 0 = lost, -1 = empty.
func (c majoritySet) voteCount(votes map[uint64]bool) int {
	if len(c) == 0 {
		return -1
	}
	yes := 0
	missing := 0
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

func definedMapReceiver() int {
	c := majoritySet{1: {}, 2: {}, 3: {}}
	votes := map[uint64]bool{1: true, 2: true, 3: false}
	return c.voteCount(votes)
}

func main() {
	fmt.Printf("{\"status\":\"ok\",\"values\":[{\"tag\":\"int\",\"value\":%d}]}\n", definedMapReceiver())
}
