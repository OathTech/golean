package main

// raft-proofs' ask G21 (2) (2026-10-26; the [USER]'s relay of the same day;
// lane core/g21-normal-form-spill-1026): an append whose SPILL would build a
// backing past the interpreter's footprint budget (arrayFootprintBudget,
// 1<<24 scalar leaves — GoLean/GoCore/Machine.lean, beside sliceCapBudget) is
// REFUSED BY NAME at the spill (cause unsupported:append-footprint-budget,
// scripts/machine-causes.tsv), after gc's own growslice panic and after the
// capacity consult — the REALIZED capacity is what is charged, so the guard
// is the make site's at the door BUG-131's scope sentence named — before any
// backing is built. Before the guard the same spill BUILT its backing and
// died under the box's memory cap (exit 137 under CAPPED_MEM_MAX=256M for
// appendOverBudget on the base's binary; BUG-131's review F1 measured three
// doublings killed at 4G and 8G). gc grows the backing and answers.
//
//   appendOverBudget     — s := make([][1024]byte, n), n = 1<<14 (exactly the
//                          budget, admitted by make); s = append(s, s...):
//                          the new length is 2^15 rows = 2^25 leaves, over the
//                          budget at EVERY capacity in the envelope. RED BY
//                          DESIGN (gc 32768).
//   appendGrowOverBudget — s at 1<<13 rows, append 1<<13 rows: the new LENGTH
//                          is exactly the budget (2^24 leaves, what make
//                          admits), but gc's realized capacity (16736 rows:
//                          nextslicecap 8192 → 16732, page-rounded) is over
//                          it — the REALIZED capacity is what is built and
//                          charged. RED BY DESIGN at the default tape (gc
//                          16384).
//   appendAtBudgetSpill  — s at 1<<13 rows, append 1<<12 rows: a spill (new
//                          length 12288 > cap 8192) whose realized capacity
//                          (13232 rows = 13,549,568 leaves) is inside the
//                          budget: PASS — the in-budget spill control.
//   appendSmallElem      — []byte at 1<<15, appended to itself: 2^16 leaves,
//                          PASS — the element footprint is what the count
//                          misses.
//   appendInPlace        — make([][1024]byte, 1, n), n = 1<<14, then one
//                          append: in place (capacity reserved), no spill,
//                          the guard is never consulted: PASS.

func appendOverBudget() int {
	n := 1 << 14
	s := make([][1024]byte, n)
	s[0][0] = 7
	s = append(s, s...)
	return len(s) + int(s[0][0]) + int(s[n][0])
}

func appendGrowOverBudget() int {
	n := 1 << 13
	s := make([][1024]byte, n)
	s[0][0] = 7
	s = append(s, s...)
	return len(s) + int(s[0][0]) + int(s[n][0])
}

func appendAtBudgetSpill() int {
	n := 1 << 13
	s := make([][1024]byte, n)
	t := make([][1024]byte, n/2)
	s[0][0] = 7
	t[0][0] = 9
	s = append(s, t...)
	return len(s) + int(s[0][0]) + int(s[n][0])
}

func appendSmallElem() int {
	n := 1 << 15
	s := make([]byte, n)
	s[0] = 7
	s = append(s, s...)
	return len(s) + int(s[0]) + int(s[n])
}

func appendInPlace() int {
	n := 1 << 14
	s := make([][1024]byte, 1, n)
	s[0][0] = 7
	var row [1024]byte
	row[0] = 9
	s = append(s, row)
	return len(s) + cap(s) + int(s[0][0]) + int(s[1][0])
}

func main() {
	println(appendAtBudgetSpill(), appendSmallElem(), appendInPlace())
}
