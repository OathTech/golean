// GoLean imported-goose corpus case — upstream bodies VERBATIM.
// source: testdata/examples/semantics/conversions.go @ 3be88bbb4982f58e5813b6f0344302d5582c8e8a
// imported: 2026-08-08 by scripts/import-goose
// transform: package clause -> main; assembly order as listed; all
// GoLean-authored code sits below the harness marker.
package main


// helpers

func literalCast() uint64 {
	// produces a uint64 -> uint64 conversion
	x := uint64(2)
	return x + 2
}

func stringToByteSlice(s string) []byte {
	// must be lifted, impure operation
	p := []byte(s)
	return p
}

func byteSliceToString(p []byte) string {
	// must be lifted, impure operation
	return string(p)
}

// tests
func testByteSliceToString() bool {
	x := make([]byte, 3)
	x[0] = 65
	x[1] = 66
	x[2] = 67
	return byteSliceToString(x) == "ABC"
}

// --- GoLean harness ---
// One int subject per upstream boolean oracle (true -> 1, false -> 0).

func goleanTestByteSliceToString() int {
	if testByteSliceToString() {
		return 1
	}
	return 0
}

func main() {}
