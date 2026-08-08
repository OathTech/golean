// GoLean imported-goose corpus case — upstream bodies VERBATIM.
// source: testdata/examples/semantics/vars.go @ 3be88bbb4982f58e5813b6f0344302d5582c8e8a
// imported: 2026-08-08 by scripts/import-goose
// transform: package clause -> main; assembly order as listed; all
// GoLean-authored code sits below the harness marker.
package main


func testPointerAssignment() bool {
	var x bool
	x = true
	return x
}

func testAddressOfLocal() bool {
	var x = false
	xptr := &x
	*xptr = true
	return x && *xptr
}

func testAnonymousAssign() bool {
	_ = uint64(1) + uint64(2)
	return true
}

// --- GoLean harness ---
// One int subject per upstream boolean oracle (true -> 1, false -> 0).

func goleanTestPointerAssignment() int {
	if testPointerAssignment() {
		return 1
	}
	return 0
}

func goleanTestAddressOfLocal() int {
	if testAddressOfLocal() {
		return 1
	}
	return 0
}

func goleanTestAnonymousAssign() int {
	if testAnonymousAssign() {
		return 1
	}
	return 0
}

func main() {}
