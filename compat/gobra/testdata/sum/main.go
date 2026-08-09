package main

// Spike subject: the Gobra tutorial `sum` example
// (deps/gobra/docs/tutorial.md §Basic Annotations / §Total Correctness,
// src/test/resources/regressions/examples/tutorial-examples/), transcribed
// as canonical Go with the contract in Gobra's annotated-.go form (`//@`,
// the Gobrafier convention). The file stays valid Go — `go run` and the
// differential oracle see only comments; Gobra sees a full contract; the
// golean spike compiles the same contract to a Surface-layer statement.

//@ requires 0 <= n
//@ ensures  sum == n * (n+1) / 2
//@ decreases
func sum(n int) (sum int) {
	sum = 0
	//@ invariant 0 <= i && i <= n + 1
	//@ invariant sum == i * (i-1) / 2
	//@ decreases n - i
	for i := 0; i <= n; i++ {
		sum += i
	}
	return sum
}

// Corpus-style nullary subjects (drivers for the differential harness and
// concrete-readout theorems).
func sumZero() int   { return sum(0) }
func sumOne() int    { return sum(1) }
func sumFive() int   { return sum(5) }
func sumTwelve() int { return sum(12) }
