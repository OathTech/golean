// GoLean imported-goose corpus case — upstream bodies VERBATIM.
// source: testdata/examples/semantics/multiple_assign.go @ 3be88bbb4982f58e5813b6f0344302d5582c8e8a
// imported: 2026-08-08 by scripts/import-goose
// transform: package clause -> main; assembly order as listed; all
// GoLean-authored code sits below the harness marker.
package main


func multReturnTwo() (uint64, uint64) {
	return 2, 3
}

func testAssignTwo() bool {
	var x uint64 = 10
	var y uint64 = 15
	x, y = multReturnTwo()
	return x == 2 && y == 3
}

func multReturnThree() (uint64, bool, uint32) {
	return 2, true, 1
}

func testAssignThree() bool {
	var x uint64 = 10
	var y bool = false
	var z uint32 = 15
	x, y, z = multReturnThree()
	return x == 2 && y == true && z == 1
}

func testMultipleAssignToMap() bool {
	var x uint64 = 10
	var m = make(map[uint64]uint64)
	x, m[0] = multReturnTwo()
	return x == 2 && m[0] == 3
}

// --- GoLean harness ---
// One int subject per upstream boolean oracle (true -> 1, false -> 0).

func goleanTestAssignTwo() int {
	if testAssignTwo() {
		return 1
	}
	return 0
}

func goleanTestAssignThree() int {
	if testAssignThree() {
		return 1
	}
	return 0
}

func goleanTestMultipleAssignToMap() int {
	if testMultipleAssignToMap() {
		return 1
	}
	return 0
}

func main() {}
