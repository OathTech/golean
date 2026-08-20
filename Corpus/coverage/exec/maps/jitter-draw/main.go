package main

// The election-jitter CHOICE SITE shape (raft W4.1 item 3, H-15 —
// docs/raft-w41-log.md; the subject-tree D-11 patch in
// tools/raftsubject/derive.py carries EXACTLY this draw inside
// (*lockedRand).Intn). The draw is the first key of a range over a
// fresh n-key map: under the machine that is the map-iteration choice
// site, under `go run` it is Go's randomized iteration order — the
// envelope is [0, n) on both oracles, and the composed observable
// realizes raft's own contract range [electionTimeout,
// 2*electionTimeout) (harness design §5's H-15 ruling: the RANGE is
// what gets the latitude entry; crypto/rand + math/big are never
// modeled). Membership row: the admitted set IS the range.
func jitterDraw() int {
	electionTimeout := 5
	n := electionTimeout
	draws := make(map[int]struct{}, n)
	for i := 0; i < n; i++ {
		draws[i] = struct{}{}
	}
	v := 0
	for k := range draws {
		v = k
		break
	}
	return electionTimeout + v
}

func main() {
	jitterDraw()
}
