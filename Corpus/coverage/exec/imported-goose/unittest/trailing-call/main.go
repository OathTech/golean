// GoLean imported-goose corpus case — upstream bodies VERBATIM.
// source: testdata/examples/unittest/trailing_call.go @ 3be88bbb4982f58e5813b6f0344302d5582c8e8a
// imported: 2026-08-08 by scripts/import-goose
// transform: package clause -> main; assembly order as listed; all
// GoLean-authored code sits below the harness marker.
package main


func mkInt() uint64 {
	return 42
}

func mkNothing() {
	mkInt()
}

// --- GoLean harness ---
// Authored wrapper (unittest tree has no oracles; scoping B.3 shape:
// a checksum/observable computed from the upstream functions).

func goleanTrailingCall() int {
	mkNothing()
	return int(mkInt())
}

func main() {}
