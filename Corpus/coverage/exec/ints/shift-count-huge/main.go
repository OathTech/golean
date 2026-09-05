package main

// Surfaced by the gotest triage re-run of stdlib slice 3 (2026-09-04;
// $GOROOT/test/fixedbugs/bug356.go): a left shift by a count that exceeds
// the operand width by a lot (1<<32, 1<<40) — spec#Operators: "shifts
// behave as if the left operand is shifted n times by 1", so an int shifts
// to 0. The machine computed 2^count in Nat and DIED (INTERNAL PANIC:
// Nat.pow exponent is too big) — a robustness bug, BUGS.md BUG-096.
func shiftCountHuge() (int, int, uint64, int) {
	var i uint64 = 1 << 32
	x := 12345
	var j uint64 = 70
	var u uint64 = 1
	var big uint64 = 1 << 40
	return x << i, x << j, u << big, -x >> i
}
