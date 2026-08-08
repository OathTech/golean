// GoLean imported-goose corpus case — upstream bodies VERBATIM.
// source: testdata/examples/semantics/block.go @ 3be88bbb4982f58e5813b6f0344302d5582c8e8a
// imported: 2026-08-08 by scripts/import-goose
// transform: package clause -> main; assembly order as listed; all
// GoLean-authored code sits below the harness marker.
package main


func testExplicitBlockStmt() bool {
	x := 10
	{
		x := 11
		x += 1
	}
	return (x == 10)
}

// --- GoLean harness ---
// One int subject per upstream boolean oracle (true -> 1, false -> 0).

func goleanTestExplicitBlockStmt() int {
	if testExplicitBlockStmt() {
		return 1
	}
	return 0
}

func main() {}
