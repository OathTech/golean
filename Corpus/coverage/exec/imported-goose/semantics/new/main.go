// GoLean imported-goose corpus case — upstream bodies VERBATIM.
// source: testdata/examples/semantics/new.go @ 3be88bbb4982f58e5813b6f0344302d5582c8e8a
// imported: 2026-08-08 by scripts/import-goose
// transform: package clause -> main; assembly order as listed; all
// GoLean-authored code sits below the harness marker.
package main


func testNilDefault() bool {
	x := new(int)
	*x = 1
	return true
}

func testNilVal() bool {
	x := new(3)
	return *x == 3
}

// --- GoLean harness ---
// One int subject per upstream boolean oracle (true -> 1, false -> 0).

func goleanTestNilDefault() int {
	if testNilDefault() {
		return 1
	}
	return 0
}

func goleanTestNilVal() int {
	if testNilVal() {
		return 1
	}
	return 0
}

func main() {}
