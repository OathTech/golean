package main

// gc's realized append-spill capacity ABOVE the growth formula by
// size-class rounding: []int oldCap 100 -> newLen 101, formula 200,
// realized cap = roundupsize(201*8)/8 = 224 (go1.26.5, probe-verified)
// — outside the old growth+[0,8) window. The widened envelope's upper
// bound 2*growth covers size-class rounding (worst class step ratio
// 48/33 < 1.5 for allocations over 32 bytes). Membership, samples=1
// (arc-final audit F2).
func appendSpillSizeClass() int {
	s := make([]int, 100, 100)
	s = append(s, 1)
	return cap(s)
}
