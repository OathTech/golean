// GoLean imported-goose corpus case — upstream bodies VERBATIM.
// source: testdata/examples/semantics/defer.go @ 3be88bbb4982f58e5813b6f0344302d5582c8e8a
// imported: 2026-08-08 by scripts/import-goose
// transform: package clause -> main; assembly order as listed; all
// GoLean-authored code sits below the harness marker.
package main


func deferSimple() *uint64 {
	x := new(uint64)
	for i := uint64(0); i < 10; i++ {
		defer func() {
			*x += 1
		}()
	}
	return x
}

func testDefer() bool {
	return *(deferSimple()) == 10
}

func testDeferFuncLit() bool {
	x := 10
	f := func() {
		defer func() {
			x += 1
		}()
	}
	f()
	return x == 11
}

// --- GoLean harness ---
// One int subject per upstream boolean oracle (true -> 1, false -> 0).

func goleanTestDefer() int {
	if testDefer() {
		return 1
	}
	return 0
}

func goleanTestDeferFuncLit() int {
	if testDeferFuncLit() {
		return 1
	}
	return 0
}

func main() {}
