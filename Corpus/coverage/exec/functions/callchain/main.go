package main

// C-05 `callchain` — the G-BIND gate instance
// (docs/2026-08-28_iris-corpus-plan.md §5.2): a nested static call
// chain with a defer. ccCaller calls ccWork bare (statement
// position — the plug-shaped call site); ccWork registers a deferred
// ccBump and calls ccDouble. The callees are resultless on purpose:
// the machine's plug barrier covers targetless, resultless frames
// (docs/g-bind-log.md D-4), so results flow through the heap (the
// *int parameter) and the caller reads the cell after the call.
//
// ccCaller(x) = 2*x + 1 + 3: ccDouble writes 2*x, the deferred
// ccBump adds 1 on the way out of ccWork, ccCaller adds 3.

func ccDouble(dst *int, x int) {
	*dst = x + x
}

func ccBump(dst *int) {
	*dst = *dst + 1
}

func ccWork(dst *int, x int) {
	defer ccBump(dst)
	ccDouble(dst, x)
}

func ccCaller(x int) int {
	y := 0
	ccWork(&y, x)
	return y + 3
}
