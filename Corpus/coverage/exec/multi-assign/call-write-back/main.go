package main

// Round-4 pins (BUG-025 REOPENED, exact scope): the multi-value CALL
// write-back path resolves target addresses — checks included — BEFORE
// the call, and stores results all-or-nothing at frame exit. gc: the
// targets' phase-1 part is only their OPERANDS; the call runs (with
// all its effects); phase 2 stores left-to-right with the target's own
// check firing per store. Three divergence shapes:
//   - a bad target must NOT suppress the call and its side effects;
//   - the CALL's own panic wins over a later target's store check;
//   - a nil FIELD target loses the first result's store.

var cwEffects int

func cwMk() (int, bool) {
	cwEffects++
	return 7, true
}

func cwRecover(fn func()) (hit int) {
	defer func() {
		if recover() != nil {
			hit = 1
		}
	}()
	fn()
	return 0
}

func callTargetSuppressesEffects() int {
	cwEffects = 0
	xs := []int{0}
	bs := []bool{false}
	hit := cwRecover(func() { xs[0], bs[5] = cwMk() })
	return hit*100 + cwEffects*10 + xs[0]
}

func cwBoom() (int, bool) {
	panic("from-call")
}

func callPanicIdentity() int {
	xs := []int{0}
	bs := []bool{false}
	xs[0], bs[5] = cwBoom()
	return 0
}

type cwT struct{ b bool }

func cwTwo() (int, bool) { return 7, true }

func callNilFieldStore() int {
	v := 0
	var p *cwT
	hit := cwRecover(func() { v, p.b = cwTwo() })
	return hit*100 + v
}

func main() {
	callTargetSuppressesEffects()
}
