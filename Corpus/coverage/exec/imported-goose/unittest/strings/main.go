// GoLean imported-goose corpus case — upstream bodies VERBATIM.
// source: testdata/examples/unittest/strings.go @ 3be88bbb4982f58e5813b6f0344302d5582c8e8a
// imported: 2026-08-08 by scripts/import-goose
// transform: package clause -> main; assembly order as listed; all
// GoLean-authored code sits below the harness marker.
package main


func stringAppend(s string) string {
	return "prefix " + s + " "
}

func stringLength(s string) uint64 {
	return uint64(len(s))
}

func x() {
	stringAppend("a" + "b")
}

// --- GoLean harness ---
// Authored wrapper.

func goleanStrings() int {
	x()
	return len(stringAppend("mid")) * 100 + int(stringLength("four"))
}

func main() {}
