package main

// Round-4 pins (BUG-037): a SINGLE assignment is a two-phase
// assignment too — the RHS is phase 1, the target's own bounds/nil
// check is phase 2 (at the store). Evaluating the full target address
// first realizes the WRONG PANIC (index/nil-deref where gc panics with
// the RHS's divide-by-zero).

type acT struct{ f int }

func indexTargetRhsPanic() int {
	a := []int{1}
	z := 0
	a[9] = 1 / z
	return a[0]
}

func nilFieldTargetRhsPanic() int {
	var p *acT
	z := 0
	p.f = 1 / z
	return 0
}

func nilDerefTargetRhsPanic() int {
	var p *int
	z := 0
	*p = 1 / z
	return 0
}

func main() {
	indexTargetRhsPanic()
}
