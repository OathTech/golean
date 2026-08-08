// GoLean imported-goose corpus case — upstream bodies VERBATIM.
// source: testdata/examples/unittest/multiple.go @ 3be88bbb4982f58e5813b6f0344302d5582c8e8a
// imported: 2026-08-08 by scripts/import-goose
// transform: package clause -> main; assembly order as listed; all
// GoLean-authored code sits below the harness marker.
package main


func returnTwo(p []byte) (uint64, uint64) {
	return 0, 0
}

func returnTwoWrapper(data []byte) (uint64, uint64) {
	a, b := returnTwo(data)
	return a, b
}

func multipleVar(x, y uint64) {}

func multiplePassThrough() {
	multipleVar(returnTwoWrapper(nil))
}

func multipleReturnPassThrough() (uint64, uint64) {
	return returnTwo(nil)
}

// --- GoLean harness ---
// Authored wrapper.

func goleanMultiple() int {
	multiplePassThrough()
	a, b := multipleReturnPassThrough()
	return int(a)*10 + int(b) + 1
}

func main() {}
