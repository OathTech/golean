// GoLean imported-goose corpus case — upstream bodies VERBATIM.
// source: testdata/examples/unittest/higher_order.go @ 3be88bbb4982f58e5813b6f0344302d5582c8e8a
// imported: 2026-08-08 by scripts/import-goose
// transform: package clause -> main; assembly order as listed; all
// GoLean-authored code sits below the harness marker.
package main


func TakesFunctionType(f func()) {
	f()
}

func FuncVar() {
	var f func()
	_ = f
}

// --- GoLean harness ---
// Authored wrapper.

func goleanHigherOrder() int {
	n := 0
	TakesFunctionType(func() { n = n + 5 })
	FuncVar()
	return n
}

func main() {}
