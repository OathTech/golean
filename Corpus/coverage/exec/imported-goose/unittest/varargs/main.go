// GoLean imported-goose corpus case — upstream bodies VERBATIM.
// source: testdata/examples/unittest/varargs.go @ 3be88bbb4982f58e5813b6f0344302d5582c8e8a
// imported: 2026-08-08 by scripts/import-goose
// transform: package clause -> main; assembly order as listed; all
// GoLean-authored code sits below the harness marker.
package main


func variadicFunc(a uint64, b string, cs ...byte) {
}

func testVariadicCall() {
	variadicFunc(10, "abc", 0, 1, 2, 3)
	variadicFunc(10, "abc")
	var c []byte
	variadicFunc(10, "abc", c...)
}

func returnMultiple() (uint64, string, uint8, uint8) {
	return 0, "xyz", 0, 0
}

func testVariadicPassThrough() {
	variadicFunc(returnMultiple())
}

// --- GoLean harness ---
// Authored wrapper.

func goleanVarargs() int {
	testVariadicCall()
	testVariadicPassThrough()
	return 1
}

func main() {}
