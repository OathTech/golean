// GoLean imported-goose corpus case — upstream bodies VERBATIM.
// source: testdata/examples/semantics/comparisons.go @ 3be88bbb4982f58e5813b6f0344302d5582c8e8a
// imported: 2026-08-08 by scripts/import-goose
// transform: package clause -> main; assembly order as listed; all
// GoLean-authored code sits below the harness marker.
package main


func testCompareAll() bool {
	var ok = true
	var nok = false

	ok = ok && (1 < 2)
	nok = ok && (2 < 1)

	ok = ok && (1 <= 2)
	ok = ok && (2 <= 2)
	nok = ok && (2 <= 1)

	if nok {
		return false
	}
	return ok
}

func testCompareGT() bool {
	var x uint64 = 4
	var y uint64 = 5

	var ok = true
	ok = ok && (y > 4)
	ok = ok && (y > x)

	return ok
}

func testCompareGE() bool {
	var x uint64 = 4
	var y uint64 = 5

	var ok = true
	ok = ok && (y >= 4)
	ok = ok && (y >= 5)
	ok = ok && (y >= x)

	if y > 5 {
		return false
	}

	return ok
}

func testCompareLT() bool {
	var x uint64 = 4
	var y uint64 = 5

	var ok = true
	ok = ok && (y < 6)
	ok = ok && (x < y)

	return ok
}

func testCompareLE() bool {
	var x uint64 = 4
	var y uint64 = 5

	var ok = true
	ok = ok && (y <= 6)
	ok = ok && (y <= 5)
	ok = ok && (x <= y)

	if y < 5 {
		return false
	}

	return ok
}

// --- GoLean harness ---
// One int subject per upstream boolean oracle (true -> 1, false -> 0).

func goleanTestCompareAll() int {
	if testCompareAll() {
		return 1
	}
	return 0
}

func goleanTestCompareGT() int {
	if testCompareGT() {
		return 1
	}
	return 0
}

func goleanTestCompareGE() int {
	if testCompareGE() {
		return 1
	}
	return 0
}

func goleanTestCompareLT() int {
	if testCompareLT() {
		return 1
	}
	return 0
}

func goleanTestCompareLE() int {
	if testCompareLE() {
		return 1
	}
	return 0
}

func main() {}
