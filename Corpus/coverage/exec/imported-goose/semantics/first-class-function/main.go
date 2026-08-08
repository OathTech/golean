// GoLean imported-goose corpus case — upstream bodies VERBATIM.
// source: testdata/examples/semantics/first_class_function.go @ 3be88bbb4982f58e5813b6f0344302d5582c8e8a
// imported: 2026-08-08 by scripts/import-goose
// transform: package clause -> main; assembly order as listed; all
// GoLean-authored code sits below the harness marker.
package main


func FirstClassFunction(a uint64) uint64 {
	return a + 10
}

func ApplyF(a uint64, f func(uint64) uint64) uint64 {
	return f(a)
}

func testFirstClassFunction() bool {
	return ApplyF(1, FirstClassFunction) == 11
}

// --- GoLean harness ---
// One int subject per upstream boolean oracle (true -> 1, false -> 0).

func goleanTestFirstClassFunction() int {
	if testFirstClassFunction() {
		return 1
	}
	return 0
}

func main() {}
