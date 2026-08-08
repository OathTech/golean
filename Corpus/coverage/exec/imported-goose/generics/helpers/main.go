// GoLean imported-goose corpus case — upstream bodies VERBATIM.
// source: testdata/examples/unittest/generics/helpers/helpers.go @ 3be88bbb4982f58e5813b6f0344302d5582c8e8a
// imported: 2026-08-08 by scripts/import-goose
// transform: package clause -> main; assembly order as listed; all
// GoLean-authored code sits below the harness marker.
package main


func AnyPointer[T any](x *T) {
}

// --- GoLean harness ---
// Authored wrapper: the any-pointer generic helper.

func goleanAnyPointer() int {
	x := 7
	AnyPointer(&x)
	return x
}

func main() {}
