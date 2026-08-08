// GoLean imported-goose corpus case — upstream bodies VERBATIM.
// source: testdata/examples/unittest/reassign.go @ 3be88bbb4982f58e5813b6f0344302d5582c8e8a
// imported: 2026-08-08 by scripts/import-goose
// transform: package clause -> main; assembly order as listed; all
// GoLean-authored code sits below the harness marker.
package main


type composite struct {
	a uint64
	b uint64
}

func ReassignVars() {
	var x uint64
	y := uint64(0)
	x = 3
	var z = composite{a: x, b: y}
	z = composite{a: y, b: x}
	x = z.a
}

// --- GoLean harness ---
// Authored wrapper (unittest tree has no oracles; scoping B.3 shape:
// a checksum/observable computed from the upstream functions).

func goleanReassignVars() int {
	ReassignVars()
	return 1
}

func main() {}
