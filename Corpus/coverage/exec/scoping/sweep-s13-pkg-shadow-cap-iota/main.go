package main

// Sweep lane sweep/s13-binding (2026-10-27), shape S13: PACKAGE-LEVEL shadows
// of predeclared identifiers — `cap` as a function and `iota` as a constant
// that a later const block then reads (the universe's iota is shadowed for the
// whole package, so `x = iota` reads the package constant). The other
// package-level shadows of the matrix (len, true, nil, false, bool) cannot be
// rowed: the oracle harness is generated INTO the subject's package and uses
// those names itself; they are hand probes (the lane's report). Expected = gc.

func cap(s []int) int { return 99 }

const iota = 10

const (
	x = iota
	y
)

// B4
func capPkgFunc() int { return cap([]int{1, 2, 3}) } // 99

// B10b
func iotaPkgConst() int { return x*100 + y } // 1010

func main() { println(capPkgFunc(), iotaPkgConst()) }
