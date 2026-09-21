package main

// E1 (Stage E, family E1 — package-level variables as READ occurrences, lane
// core/unseq-stage-e-0921, 2026-09-21): v := mut() + g with g a PACKAGE-LEVEL
// variable mut writes. The read of g is spec-unsequenced against the call
// (spec#Order_of_evaluation): {1, 2}; gc 2 (call-first). The reference is
// enumerate.py's E1a.
var g = 1

func e1() int {
	mut := func() int { g = 2; return 0 }
	v := mut() + g
	return v
}

func main() { println(e1()) }
