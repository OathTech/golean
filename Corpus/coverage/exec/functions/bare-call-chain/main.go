package main

// BUG-012's dominant real-Go shapes, pinned at the arc-final audit's
// re-pricing (F11, 2026-08-06): a bare statement-position call whose
// callee RETURNS values — method chaining, a helper called for its
// side effect, and the same through a func VALUE. The frame-exit step
// used to go stuck ("extra GoCore assignment value") because the
// targetless call still pinned the callee's result locations.

type bccWidget struct {
	total int
}

func (w *bccWidget) add(s string) *bccWidget {
	w.total += len(s)
	return w
}

// Method chaining: the OUTER call's result is discarded.
func bareCallChain() int {
	w := &bccWidget{}
	w.add("a").add("bc")
	return w.total
}

var bccCount int

func bccBump() int {
	bccCount++
	return 3
}

// Plain helper called bare for its side effect.
func bareCallHelper() int {
	bccBump()
	bccBump()
	return bccCount
}

// The same through a func value.
func bareCallFuncValue() int {
	f := bccBump
	f()
	return 1
}

// Multi-result callee discarded bare.
func bccPair() (int, string) {
	bccCount += 10
	return 1, "x"
}

func bareCallMultiResult() int {
	before := bccCount
	bccPair()
	return bccCount - before
}
