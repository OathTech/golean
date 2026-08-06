package main

// Convergence-round pins (BUG-029, select forms): a selected receive
// clause's user assignment follows the SAME §Assignments two-phase
// split as the receive statement (spec §Select statements step 4) —
// phase 1 evaluates the target address operands after the
// communication, phase 2 stores left-to-right with the outer
// nil/bounds check a store-time event. The statement-form
// discriminators live in channels/recv-edge; these pin the select
// path, which must not diverge from it.

func selDepIndexTarget() int {
	ch := make(chan int, 1)
	ch <- 3
	i := 0
	bs := []bool{false, false, false, false}
	select {
	case i, bs[i] = <-ch:
	}
	n := i * 100
	for j := range bs {
		if bs[j] {
			n += j + 1
		}
	}
	return n
}

func selNilIndexBaseSecond() int {
	ch := make(chan int, 1)
	ch <- 3
	xs := []int{0}
	var bp *[]bool
	hit := 0
	func() {
		defer func() {
			if recover() != nil {
				hit = 1
			}
		}()
		select {
		case xs[0], (*bp)[0] = <-ch:
		}
	}()
	return hit*1000 + xs[0]*50
}

type selT struct{ b bool }

func selFieldSecondTarget() int {
	ch := make(chan int, 1)
	ch <- 3
	xs := []int{0}
	var p *selT
	hit := 0
	func() {
		defer func() {
			if recover() != nil {
				hit = 1
			}
		}()
		select {
		case xs[0], p.b = <-ch:
		}
	}()
	return hit*1000 + xs[0]*50
}

func main() {
	selDepIndexTarget()
}

// Round-4 pin (BUG-033, select path): same chain deferral through the
// clause-head machine targets.
type selChainT struct{ b bool }

func selChainFieldOverIndex() int {
	ch := make(chan int, 1)
	ch <- 3
	xs := []int{0}
	a := []selChainT{}
	hit := 0
	func() {
		defer func() {
			if recover() != nil {
				hit = 1
			}
		}()
		select {
		case xs[0], a[9].b = <-ch:
		}
	}()
	return hit*1000 + xs[0]*50
}

// Round-4 pin (BUG-036): the temp-FALLBACK lowering (taken when a
// clause target's emission hoists — here idx() in the second target's
// index) must preserve the phase split: idx() reads the PRE-store gi.
// Per-target single assigns store gi before evaluating idx().
var selGi int

func selIdx() int { return selGi }

func selFallbackCallIndex() int {
	ch := make(chan int, 1)
	ch <- 3
	selGi = 1
	xs := []bool{false, false, false}
	select {
	case selGi, xs[selIdx()] = <-ch:
	}
	n := selGi * 10
	for j := range xs {
		if xs[j] {
			n += j + 1
		}
	}
	return n
}
