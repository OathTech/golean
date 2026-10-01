package main

// The RETIRED election-jitter idiom (raft W4.1 item 3, H-15 —
// docs/raft-w41-log.md). Until window unit 5b the D-11 patch in
// tools/raftsubject/derive.py carried this draw inside
// (*lockedRand).Intn; since 5b (D6) it calls the general native site
// `rand.Intn(n)` instead (builtins/rand-intn/jitter-shape pins that
// shape). The draw is the first key of a range over a fresh n-key map:
// under the machine the map-iteration choice site, under `go run` Go's
// randomized iteration order — the envelope is [0, n) on both oracles,
// and the composed observable realizes raft's contract range
// [electionTimeout, 2*electionTimeout). Kept as the pin of the map-range
// shape. Membership row: the admitted set IS the range.
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
