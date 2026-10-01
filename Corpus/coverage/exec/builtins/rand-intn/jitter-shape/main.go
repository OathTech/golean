package main

import "math/rand"

// The election-jitter shape over the native site — raft's
// `resetRandomizedElectionTimeout` (`r.electionTimeout + globalRand.Intn(
// r.electionTimeout)`) with the D-11 subject patch RE-KEYED onto this draw
// (tools/raftsubject/derive.py, 2026-09-30; the predecessor guardrail
// `maps/jitter-draw` pins the retired map-range idiom). Membership row: the
// composed observable realizes raft's contract range [electionTimeout,
// 2*electionTimeout) — admitted set {5,6,7,8,9} at timeout 5, all members
// exhibited by the machine, every go-run sample inside.
func jitter() int {
	electionTimeout := 5
	return electionTimeout + rand.Intn(electionTimeout)
}

func main() {
	println(jitter())
}
