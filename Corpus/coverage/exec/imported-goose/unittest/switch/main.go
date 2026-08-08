// GoLean imported-goose corpus case — upstream bodies VERBATIM.
// source: testdata/examples/unittest/switch.go @ 3be88bbb4982f58e5813b6f0344302d5582c8e8a
// imported: 2026-08-08 by scripts/import-goose
// transform: package clause -> main; assembly order as listed; all
// GoLean-authored code sits below the harness marker.
package main


func testSwitchVal(x uint64) bool {
	switch x {
	default:
		return false
	case 0:
		return true
	case 1:
		return false
	}
}

func testSwitchMultiple(x uint64) int {
	switch x {
	case 10, 1:
		return 1
	case 0:
		return 2
	}
	return 3
}

// --- GoLean harness ---
// Authored wrapper.

func goleanSwitch() int {
	sum := 0
	if testSwitchVal(0) {
		sum++
	}
	if testSwitchVal(1) {
		sum += 2
	}
	return sum + testSwitchMultiple(10)*10 + testSwitchMultiple(0)*100 + testSwitchMultiple(7)*1000
}

func main() {}
