// GoLean imported-goose corpus case — upstream bodies VERBATIM.
// source: testdata/examples/mapliteral/mapliteral.go @ 3be88bbb4982f58e5813b6f0344302d5582c8e8a
// imported: 2026-08-08 by scripts/import-goose
// transform: package clause -> main; assembly order as listed; all
// GoLean-authored code sits below the harness marker.
package main


func f() uint64 {
	return 1
}

type Nested struct {
	X uint64
}

func mapliteral() map[uint64]uint64 {
	return map[uint64]uint64{1: 2}
}

func nestedMapLiteral() map[uint64]Nested {
	return map[uint64]Nested{
		1: {X: f()},
	}
}

// --- GoLean harness ---
// Authored wrapper: both map-literal shapes, keyed readout.

func goleanMapLiteral() int {
	m := mapliteral()
	n := nestedMapLiteral()
	return int(m[1]*10 + n[1].X)
}

func main() {}
