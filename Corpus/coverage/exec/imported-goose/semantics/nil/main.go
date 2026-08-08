// GoLean imported-goose corpus case — upstream bodies VERBATIM.
// source: testdata/examples/semantics/nil.go @ 3be88bbb4982f58e5813b6f0344302d5582c8e8a
// imported: 2026-08-08 by scripts/import-goose
// transform: package clause -> main; assembly order as listed; all
// GoLean-authored code sits below the harness marker.
package main


func testCompareSliceToNil() bool {
	s := make([]byte, 0)
	return s != nil
}

func testComparePointerToNil() bool {
	s := new(uint64)
	return s != nil
}

func testCompareNilToNil() bool {
	s := new(*uint64)
	return *s == nil
}

func testComparePointerWrappedToNil() bool {
	var s []byte
	s = make([]byte, 1)
	return s != nil
}

func testComparePointerWrappedDefaultToNil() bool {
	var s []byte
	return s == nil
}

func testInterfaceNilWithType() bool {
	// subtlety in Go: nil interface vs interface with a nil pointer in it are
	// different
	var isNil any = nil
	var notNil any = (*string)(nil)
	return isNil == nil && notNil != nil && isNil != notNil
}

// --- GoLean harness ---
// One int subject per upstream boolean oracle (true -> 1, false -> 0).

func goleanTestCompareSliceToNil() int {
	if testCompareSliceToNil() {
		return 1
	}
	return 0
}

func goleanTestComparePointerToNil() int {
	if testComparePointerToNil() {
		return 1
	}
	return 0
}

func goleanTestCompareNilToNil() int {
	if testCompareNilToNil() {
		return 1
	}
	return 0
}

func goleanTestComparePointerWrappedToNil() int {
	if testComparePointerWrappedToNil() {
		return 1
	}
	return 0
}

func goleanTestComparePointerWrappedDefaultToNil() int {
	if testComparePointerWrappedDefaultToNil() {
		return 1
	}
	return 0
}

func goleanTestInterfaceNilWithType() int {
	if testInterfaceNilWithType() {
		return 1
	}
	return 0
}

func main() {}
