// GoLean imported-goose corpus case — upstream bodies VERBATIM.
// source: testdata/examples/semantics/builtin.go @ 3be88bbb4982f58e5813b6f0344302d5582c8e8a
// imported: 2026-08-08 by scripts/import-goose
// transform: package clause -> main; assembly order as listed; all
// GoLean-authored code sits below the harness marker.
package main


func testMinUint64() bool {
	x := uint64(10)
	return min(x, 1) == 1
}

func testMaxUint64() bool {
	x := uint64(10)
	return max(x, 1) == 10
}

// --- GoLean harness ---
// One int subject per upstream boolean oracle (true -> 1, false -> 0).

func goleanTestMinUint64() int {
	if testMinUint64() {
		return 1
	}
	return 0
}

func goleanTestMaxUint64() int {
	if testMaxUint64() {
		return 1
	}
	return 0
}

func main() {}
