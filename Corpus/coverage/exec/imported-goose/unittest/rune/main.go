// GoLean imported-goose corpus case — upstream bodies VERBATIM.
// source: testdata/examples/unittest/rune.go @ 3be88bbb4982f58e5813b6f0344302d5582c8e8a
// imported: 2026-08-08 by scripts/import-goose
// transform: package clause -> main; assembly order as listed; all
// GoLean-authored code sits below the harness marker.
package main


func useRuneOps(r rune) rune {
	r++
	r = 'a'
	r = 47
	x := int32(rune('b'))
	r = rune(x)
	return r
}

// --- GoLean harness ---
// Authored wrapper.

func goleanRuneOps() int {
	return int(useRuneOps('x'))
}

func main() {}
