// GoLean imported-goose corpus case — upstream bodies VERBATIM.
// source: testdata/examples/semantics/precedence.go @ 3be88bbb4982f58e5813b6f0344302d5582c8e8a
// imported: 2026-08-08 by scripts/import-goose
// transform: package clause -> main; assembly order as listed; all
// GoLean-authored code sits below the harness marker.
package main


func testOrCompareSimple() bool {
	if 3 > 4 || 4 > 3 {
		return true
	}
	return false
}

func testOrCompare() bool {
	var ok = true
	if !(3 > 4 || 4 > 3) {
		ok = false
	}
	if 4 < 3 || 2 > 3 {
		ok = false
	} else {
	}
	return ok
}

func testAndCompare() bool {
	var ok = true
	if 3 > 4 && 4 > 3 {
		ok = false
	}
	if 4 > 3 || 2 < 3 {
	} else {
		ok = false
	}
	return ok
}

func testShiftMod() bool {
	return (20 >> (8 % 4)) == 20
}

// --- GoLean harness ---
// One int subject per upstream boolean oracle (true -> 1, false -> 0).

func goleanTestOrCompareSimple() int {
	if testOrCompareSimple() {
		return 1
	}
	return 0
}

func goleanTestOrCompare() int {
	if testOrCompare() {
		return 1
	}
	return 0
}

func goleanTestAndCompare() int {
	if testAndCompare() {
		return 1
	}
	return 0
}

func goleanTestShiftMod() int {
	if testShiftMod() {
		return 1
	}
	return 0
}

func main() {}
