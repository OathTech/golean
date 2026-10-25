package main

// Release-readiness row 31(d) ([USER] ruling 2026-10-25, relayed by the
// [AGENT] coordinator; lane core/row31-fillers-1025): a `make` whose count
// is a RUN-TIME value and whose count × element footprint is past the
// interpreter's footprint budget (arrayFootprintBudget, 1<<24 scalar
// leaves — GoLean/GoCore/Machine.lean, beside sliceCapBudget) is REFUSED
// BY NAME at the make site (cause unsupported:make-footprint-budget-runtime,
// scripts/machine-causes.tsv), after gc's own makeslice panic and after
// sliceCapBudget's count bound, before any backing is built. Before the
// guard such a make BUILT its backing and died under the box's memory
// cap: exit 137 at 4G in 0.4 s and at 8G in 6.3 s for a 1<<19-row twin of
// makeOverBudget (the lane's reproduction on main 541d8340's binary) — a
// loud apparatus kill, never a named refusal, and on a machine without
// the cap a memory runaway. The CONSTANT-count twin of each shape refuses
// at decode / per declaration since 2026-10-12/13
// (arrays/materialization-budget-make/, arrays/materialization-budget-
// quarantine/); the counts here are variables, which neither the
// frontend's nor the decoder's constant check reads, so every row below
// reaches the machine. BUG-131.
//
//   makeOverBudget    — make([][1024]byte, n), n = 1<<15: 2^25 leaves, over
//                       the budget. RED BY DESIGN (gc allocates the 32 MiB
//                       and answers 32775).
//   makeCapOverBudget — make([][1024]byte, 1, n), n = 1<<15: the CAP sizes
//                       the backing. RED BY DESIGN (gc 32775).
//   makeAtBudget      — make([][1024]byte, n), n = 1<<14: exactly 1<<24
//                       leaves, admitted (strict `>`), PASS — the budget's
//                       edge from the run-time side (the constant side is
//                       materialization-budget-admitted/make-at-budget).
//   makeSmallElem     — make([]byte, n), n = 1<<15: 2^15 leaves, PASS — the
//                       element footprint is what the count-only bound
//                       (sliceCapBudget) misses, and a scalar element at
//                       the refused rows' count is far inside the budget.
//   makeMaxAllocFirst — make([][1024]byte, n), n = 1<<40: 2^50 bytes, past
//                       gc's maxAlloc — gc's OWN `makeslice: len out of
//                       range` panic on both sides (status panic), never
//                       pre-empted by the guard (the make site's order:
//                       gc's panic, the count bound, then the footprint).

func makeOverBudget() int {
	n := 1 << 15
	b := make([][1024]byte, n)
	b[0][0] = 7
	return len(b) + int(b[0][0])
}

func makeCapOverBudget() int {
	n := 1 << 15
	b := make([][1024]byte, 1, n)
	b[0][0] = 7
	return cap(b) + int(b[0][0])
}

func makeAtBudget() int {
	n := 1 << 14
	b := make([][1024]byte, n)
	b[0][0] = 7
	b[len(b)-1][1023] = 9
	return len(b) + int(b[0][0]) + int(b[len(b)-1][1023])
}

func makeSmallElem() int {
	n := 1 << 15
	b := make([]byte, n)
	b[0] = 7
	b[len(b)-1] = 9
	return len(b) + int(b[0]) + int(b[len(b)-1])
}

func makeMaxAllocFirst() int {
	n := 1 << 40
	b := make([][1024]byte, n)
	return len(b)
}

func main() {
	println(makeAtBudget(), makeSmallElem())
}
