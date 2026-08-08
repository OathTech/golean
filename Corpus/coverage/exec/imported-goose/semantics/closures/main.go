// GoLean imported-goose corpus case — upstream bodies VERBATIM.
// source: testdata/examples/semantics/closures.go @ 3be88bbb4982f58e5813b6f0344302d5582c8e8a
// imported: 2026-08-08 by scripts/import-goose
// transform: package clause -> main; assembly order as listed; all
// GoLean-authored code sits below the harness marker.
package main


type AdderType = func(uint64) uint64
type MultipleArgsType = func(uint64, bool) uint64

func adder() AdderType {
	var sum = uint64(0)
	return func(x uint64) uint64 {
		sum += x
		return sum
	}
}

func testClosureBasic() bool {
	pos := adder()
	doub := adder()
	for i := uint64(0); i < 10; i++ {
		pos(i)
		doub(2 * i)
	}
	if pos(0) == 45 && doub(0) == 90 {
		return true
	}
	return false
}

// --- GoLean harness ---
// One int subject per upstream boolean oracle (true -> 1, false -> 0).

func goleanTestClosureBasic() int {
	if testClosureBasic() {
		return 1
	}
	return 0
}

func main() {}
