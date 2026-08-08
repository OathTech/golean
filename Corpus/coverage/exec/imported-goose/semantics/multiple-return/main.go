// GoLean imported-goose corpus case — upstream bodies VERBATIM.
// source: testdata/examples/semantics/multiple_return.go @ 3be88bbb4982f58e5813b6f0344302d5582c8e8a
// imported: 2026-08-08 by scripts/import-goose
// transform: package clause -> main; assembly order as listed; all
// GoLean-authored code sits below the harness marker.
package main


func returnTwo() (uint64, uint64) {
	return 2, 3
}

func testReturnTwo() bool {
	x, y := returnTwo()
	return x == 2 && y == 3
}

func testAnonymousBinding() bool {
	_, y := returnTwo()
	return y == 3
}

func returnThree() (uint64, bool, uint32) {
	return 2, true, 1
}

func testReturnThree() bool {
	x, y, z := returnThree()
	return x == 2 && y == true && z == 1
}

func returnFour() (uint64, bool, uint32, uint64) {
	return 2, true, 1, 7
}

func testReturnFour() bool {
	x, y, z, w := returnFour()
	return x == 2 && y == true && z == 1 && w == 7
}

// --- GoLean harness ---
// One int subject per upstream boolean oracle (true -> 1, false -> 0).

func goleanTestReturnTwo() int {
	if testReturnTwo() {
		return 1
	}
	return 0
}

func goleanTestAnonymousBinding() int {
	if testAnonymousBinding() {
		return 1
	}
	return 0
}

func goleanTestReturnThree() int {
	if testReturnThree() {
		return 1
	}
	return 0
}

func goleanTestReturnFour() int {
	if testReturnFour() {
		return 1
	}
	return 0
}

func main() {}
