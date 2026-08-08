// GoLean imported-goose corpus case — upstream bodies VERBATIM.
// source: testdata/examples/semantics/switch.go @ 3be88bbb4982f58e5813b6f0344302d5582c8e8a
// imported: 2026-08-08 by scripts/import-goose
// transform: package clause -> main; assembly order as listed; all
// GoLean-authored code sits below the harness marker.
package main


func testSwitchVal() bool {
	x := uint64(0)
	switch x {
	default:
		return false
	case 0:
		return true
	case 1:
		return false
	}
}

func testSwitchMultiple() bool {
	x := uint64(0)
	switch x {
	case 10, 1:
		return false
	case 0:
		return true
	}
	return false
}

func testSwitchDefaultTrue() bool {
	x := uint64(1)
	switch {
	case false:
		return false
	case x == 2:
		return false
	default:
		return true
	}
}

type switchConcrete struct {
}

type switchInterface interface {
	marker()
}

func (c *switchConcrete) marker() {
}

func testSwitchConversion() bool {
	v := &switchConcrete{}
	var x switchInterface = v
	switch x {
	case v:
	default:
		return false
	}

	switch v {
	case x:
	default:
		return false
	}
	return true
}

// --- GoLean harness ---
// One int subject per upstream boolean oracle (true -> 1, false -> 0).

func goleanTestSwitchVal() int {
	if testSwitchVal() {
		return 1
	}
	return 0
}

func goleanTestSwitchMultiple() int {
	if testSwitchMultiple() {
		return 1
	}
	return 0
}

func goleanTestSwitchDefaultTrue() int {
	if testSwitchDefaultTrue() {
		return 1
	}
	return 0
}

func goleanTestSwitchConversion() int {
	if testSwitchConversion() {
		return 1
	}
	return 0
}

func main() {}
