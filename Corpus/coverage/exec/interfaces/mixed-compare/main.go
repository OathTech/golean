package main

// Mixed interface/non-interface comparison — the Go spec's own bullet
// (§Comparison operators): "A value x of non-interface type X and a
// value t of interface type T can be compared if type X is comparable
// and X implements T. They are equal if t's dynamic type is identical
// to X and t's dynamic value is equal to x." The interface wrap was
// emitted at every assignable slot EXCEPT comparison operands and
// switch-case slots, so every one of these shapes refused
// (fail-closed) instead of answering. Includes the two dominant idioms:
// switch-on-any with concrete cases and the sentinel-error comparison.
// Arc-final audit F4 (2026-08-06), red-first.

func mixedEqIntLit() int {
	var i any = 5
	if i == 5 {
		return 1
	}
	return 0
}

func mixedEqIntLitReversed() int {
	var i any = 5
	if 5 == i {
		return 1
	}
	return 0
}

func mixedNeqMiss() int {
	var i any = "s"
	if i != 5 {
		return 1
	}
	return 0
}

func mixedSwitchCase() int {
	var i any = 5
	switch i {
	case 4:
		return 40
	case 5:
		return 50
	}
	return 0
}

type mcErr struct{ s string }

func (e *mcErr) Error() string { return e.s }

var mcSentinel = &mcErr{"sentinel"}

func mixedSentinelError() int {
	var err error = mcSentinel
	if err == mcSentinel {
		return 11
	}
	return 0
}

func mixedSentinelErrorReversed() int {
	var err error = mcSentinel
	if mcSentinel == err {
		return 11
	}
	return 0
}

type mcPoint struct{ x, y int }

func mixedStructBothOrders() int {
	var i any = mcPoint{2, 3}
	n := 0
	if i == (mcPoint{2, 3}) {
		n += 50
	}
	if (mcPoint{2, 3}) == i {
		n += 5
	}
	return n
}

// CONTROL: interface-to-interface comparison, already supported.
func mixedCtlIfaceIface() int {
	var a any = 7
	var b any = 7
	if a == b {
		return 1
	}
	return 0
}
