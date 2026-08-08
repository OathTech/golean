// GoLean imported-goose corpus case — upstream bodies VERBATIM.
// source: testdata/examples/unittest/control_flow.go @ 3be88bbb4982f58e5813b6f0344302d5582c8e8a
// imported: 2026-08-08 by scripts/import-goose
// transform: package clause -> main; assembly order as listed; all
// GoLean-authored code sits below the harness marker.
package main


func conditionalReturn(x bool) uint64 {
	if x {
		return 0
	}
	return 1
}

func alwaysReturn(x bool) uint64 {
	if x {
		return 0
	} else {
		return 1
	}
}

func alwaysReturnInNestedBranches(x bool) uint64 {
	if !x {
		if x {
			return 0
		} else {
			return 1
		}
	} else {
		// we can even have an empty else block
	}
	y := uint64(14)
	return y
}

func earlyReturn(x bool) {
	if x {
		return
	}
}

func conditionalAssign(x bool) uint64 {
	var y uint64
	if x {
		y = 1
	} else {
		y = 2
	}
	y += 1
	return y
}

func elseIf(x, y bool) uint64 {
	if x {
		return 0
	} else if y {
		return 1
	} else {
		return 2
	}
}

func ifStmtInitialization(x uint64) uint64 {
	f := func() uint64 {
		return x
	}

	if f(); x == 2 {
	} else if z := x; z == 1 {
	} else if y := 94; y == 30 {
	} else if z = 10; x == 30 {
	}

	if y := uint64(10); x == 0 {
		return y
	} else {
		return y - 1
	}
}

// --- GoLean harness ---
// Authored wrapper.

func goleanControlFlow() int {
	sum := int(conditionalReturn(true)) + int(alwaysReturn(false))*10
	sum += int(alwaysReturnInNestedBranches(false)) * 100
	earlyReturn(true)
	earlyReturn(false)
	sum += int(conditionalAssign(false)) * 1000
	sum += int(elseIf(false, true)) * 10000
	sum += int(ifStmtInitialization(1)) * 100000
	return sum
}

func main() {}
