package main

// CELEM (Stage C audit fix round, F2; the audit's a15): `a[f()] = 5` — an INT
// constant copied into the phase-2 store's value cell (design §6); a is captured
// by f (its header is a READ occurrence, unordered against the call — f does not
// rebind a, so the observation is a singleton): {`f` · 59}; main's legacy ANF
// gives the same.
func celem() int {
	a := []int{1, 2}
	f := func() int { println("f"); a[1] = 9; return 0 }
	a[f()] = 5
	return a[0]*10 + a[1]
}

func main() { println(celem()) }
