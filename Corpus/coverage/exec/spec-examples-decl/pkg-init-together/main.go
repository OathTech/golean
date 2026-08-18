package main

// spec#Package_initialization block Package_initialization-1-235612be:
// within a package, initialization proceeds by repeatedly picking the
// earliest-declared READY variable — a and b are initialized TOGETHER (one
// call of f), and both before x, because x depends on a. Observable: x sees
// a's final value 1, and f runs exactly once.

var fRuns int

var x = a

var a, b = f() // a and b are initialized together, before x is initialized

func f() (int, int) {
	fRuns++
	return 1, 2
}

func pkgInitTogether() int {
	return x*1000 + a*100 + b*10 + fRuns // 1121
}
