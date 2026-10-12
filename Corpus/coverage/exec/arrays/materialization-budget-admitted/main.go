package main

// The ADMITTED side of the nested materialization budget (BUG-078
// residual (3), fail-closed 2026-10-12; residual (2b)'s decoder half at
// the fix round the same day): shapes the decoder admits and the
// machine runs inside its margin, pinned PASS so the budget's constant
// cannot drift down unnoticed. Measured on main's binary at c266ce6b,
// single runs under `capped` (the per-case wall is 60 s):
//
//   nestedAtBudget — [4096][4096]byte, exactly 1<<24 scalar elements
//     (AT the budget, admitted: the check is strict `>`), one element
//     store into the default value: 2.01 s (its literal form, the worst
//     path, 4.11 s — the budget's own derivation point).
//   makeLargeElem — make([][1024]byte, 1<<13): the element COUNT is
//     inside sliceCapBudget (1<<23, BUG-090) and the element type inside
//     both array budgets; 2^23 leaves materialize in 1.01 s.
//   makeAtBudget — make([][1024]byte, 1<<14): exactly 1<<24 leaves,
//     the constant-count make bound's own edge (checkMakeFootprint,
//     strict `>`); the time is in cases.tsv. One doubling (1<<15,
//     2^25) is over the budget and refuses; the row
//     arrays/materialization-budget-make/over-budget pins the refusal
//     at 1<<19, the reviewer's reproduced kill.
func nestedAtBudget() int {
	var a [4096][4096]byte
	a[0][0] = 42
	a[4095][4095] = 7
	return int(a[0][0]) + int(a[4095][4095])
}

func makeLargeElem() int {
	b := make([][1024]byte, 1<<13)
	b[0][0] = 7
	b[len(b)-1][1023] = 9
	return len(b) + int(b[0][0]) + int(b[len(b)-1][1023])
}

func makeAtBudget() int {
	b := make([][1024]byte, 1<<14)
	b[0][0] = 7
	b[len(b)-1][1023] = 9
	return len(b) + int(b[0][0]) + int(b[len(b)-1][1023])
}
