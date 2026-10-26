package main

// BUG-136 (the equality/identity review of 2026-10-26, F2; lane
// frontend/workspace-and-oracle-1026): untyped nil as the LEFT operand of
// `==` / `!=` — `nil == p`, `nil != err` — was refused by name for every
// operand kind («basic type untyped nil»: the frontend took the comparison's
// operand type from the left operand, and emitType has no arm for untyped
// nil) while `p == nil` lowered. Each subject scores the nil-left spellings
// beside a nil-right twin, per operand kind; expected = gc. Six subjects —
// pointer, map, slice, func, chan, switch-case — were born RED at the base
// (the subject quarantined: the machine answers `unsupported`,
// «frontend-quarantined: basic type untyped nil», stage lean-observation),
// green at the tip; the interface and error subjects are the CONTROLS, green
// at the base too: a bare nil against an interface already took the
// interface side's type through the mixed-comparison rule.

func nilLeftPointer() int {
	x := 1
	p := &x
	var np *int
	score := 0
	if nil == p {
		score += 1
	}
	if nil != p {
		score += 10
	}
	if nil == np {
		score += 100
	}
	if nil != np {
		score += 1000
	}
	if p == nil { // the nil-right twin
		score += 10000
	}
	return score
}

func nilLeftMap() int {
	m := map[int]int{}
	var nm map[int]int
	score := 0
	if nil == m {
		score += 1
	}
	if nil != m {
		score += 10
	}
	if nil == nm {
		score += 100
	}
	if nil != nm {
		score += 1000
	}
	if nm == nil {
		score += 10000
	}
	return score
}

func nilLeftSlice() int {
	s := []int{}
	var ns []int
	score := 0
	if nil == s {
		score += 1
	}
	if nil != s {
		score += 10
	}
	if nil == ns {
		score += 100
	}
	if nil != ns {
		score += 1000
	}
	if ns == nil {
		score += 10000
	}
	return score
}

func nilLeftFunc() int {
	f := func() {}
	var nf func()
	score := 0
	if nil == f {
		score += 1
	}
	if nil != f {
		score += 10
	}
	if nil == nf {
		score += 100
	}
	if nil != nf {
		score += 1000
	}
	if nf == nil {
		score += 10000
	}
	return score
}

func nilLeftInterface() int {
	var i any = 1
	var ni any
	score := 0
	if nil == i {
		score += 1
	}
	if nil != i {
		score += 10
	}
	if nil == ni {
		score += 100
	}
	if nil != ni {
		score += 1000
	}
	if ni == nil {
		score += 10000
	}
	return score
}

type nilLeftErr struct{}

func (nilLeftErr) Error() string { return "e" }

func nilLeftError() int {
	var e error
	var typed *nilLeftErr
	var boxed error = typed // a typed nil in the box: != nil
	score := 0
	if nil == e {
		score += 1
	}
	if nil != e {
		score += 10
	}
	if nil == boxed {
		score += 100
	}
	if nil != boxed {
		score += 1000
	}
	if e == nil {
		score += 10000
	}
	return score
}

func nilLeftChan() int {
	ch := make(chan int)
	var nch chan int
	score := 0
	if nil == ch {
		score += 1
	}
	if nil != ch {
		score += 10
	}
	if nil == nch {
		score += 100
	}
	if nil != nch {
		score += 1000
	}
	if nch == nil {
		score += 10000
	}
	return score
}

func nilLeftSwitchCase() int {
	var np *int
	x := 2
	p := &x
	score := 0
	switch {
	case nil == p:
		score += 1
	case nil != p && nil == np:
		score += 10
	default:
		score += 100
	}
	switch {
	case nil != np:
		score += 1000
	case p != nil && *p == 2:
		score += 10000
	}
	return score
}

func main() {
	println(nilLeftPointer(), nilLeftMap(), nilLeftSlice(), nilLeftFunc(), nilLeftInterface(), nilLeftError(), nilLeftChan(), nilLeftSwitchCase())
}
