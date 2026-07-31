package main

import "fmt"

// The vacuous-satisfaction hole (pre-merge audit 2026-07-31, finding 0) is
// GENERIC to every interface not declared in this package, not specific to the
// predeclared `error`: an IMPORTED interface referenced only as an assert
// target has no call site either.

type stringly struct{ n int }

func (s stringly) String() string { return "s" }

func assertStringerNegative() int {
	var x any = 3
	_, ok := x.(fmt.Stringer)
	if ok {
		return 1
	}
	return 0
}

func assertStringerPositive() int {
	var x any = stringly{n: 2}
	_, ok := x.(fmt.Stringer)
	if ok {
		return 1
	}
	return 0
}
