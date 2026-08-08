// GoLean imported-goose corpus case — upstream bodies VERBATIM.
// source: testdata/examples/unittest/copy.go @ 3be88bbb4982f58e5813b6f0344302d5582c8e8a
// imported: 2026-08-08 by scripts/import-goose
// transform: package clause -> main; assembly order as listed; all
// GoLean-authored code sits below the harness marker.
package main


func testCopySimple() bool {
	x := make([]byte, 10)
	x[3] = 1
	y := make([]byte, 10)
	copy(y, x)
	return y[3] == 1
}

func testCopyDifferentLengths() bool {
	x := make([]byte, 15)
	x[3] = 1
	x[12] = 2
	y := make([]byte, 10)
	n := uint64(copy(y, x))
	return n == 10 && y[3] == 1
}

// --- GoLean harness ---
// One int subject per upstream boolean oracle (true -> 1, false -> 0).

func goleanTestCopySimple() int {
	if testCopySimple() {
		return 1
	}
	return 0
}

func goleanTestCopyDifferentLengths() int {
	if testCopyDifferentLengths() {
		return 1
	}
	return 0
}

func main() {}
