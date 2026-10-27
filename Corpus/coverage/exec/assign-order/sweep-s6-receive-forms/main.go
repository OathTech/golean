package main

// S6 sweep, group R: the receive statement and select receive clauses — the
// COMMUNICATION is phase 1 (it drains the channel), the targets' own checks
// are phase 2 at their stores, left to right; a closed channel delivers the
// zero value and false into every target kind.

func rRecover(fn func()) (hit int) {
	defer func() {
		if recover() != nil {
			hit = 1
		}
	}()
	fn()
	return 0
}

func b2i(b bool) int {
	if b {
		return 1
	}
	return 0
}

// R.4: a nil-map single receive target — the receive drains, then the store panics.
func rNilMapRecvDrains() int {
	ch := make(chan int, 1)
	ch <- 7
	var m map[int]int
	hit := rRecover(func() { m[1] = <-ch })
	return hit*100 + len(ch)
}

// R.7: a CLOSED channel's comma-ok receive into two index targets: zero, false.
func rClosedCommaOkIndexTargets() int {
	ch := make(chan int, 1)
	close(ch)
	xs := []int{9}
	bs := []bool{true}
	xs[0], bs[0] = <-ch
	return xs[0]*10 + b2i(bs[0])
}

// R.8: the same into two deref targets.
func rClosedCommaOkDerefTargets() int {
	ch := make(chan int, 1)
	close(ch)
	v := 9
	ok := true
	p := &v
	q := &ok
	*p, *q = <-ch
	return v*10 + b2i(ok)
}

func rIdx(ch chan int) int { println("len", len(ch)); return 0 }

// R.9: a call in the target's index runs BEFORE the receive (both ordered
// events, left to right): it sees the channel still full.
func rCallIndexBeforeRecv() int {
	ch := make(chan int, 1)
	ch <- 7
	xs := []int{0}
	xs[rIdx(ch)] = <-ch
	return xs[0]*10 + len(ch)
}

// R.10: a call producing the deref target's pointer, before the receive.
func rCallDerefBeforeRecv() int {
	ch := make(chan int, 1)
	ch <- 7
	v := 0
	pf := func() *int { println("len", len(ch)); return &v }
	*pf() = <-ch
	return v*10 + len(ch)
}

// R.27: a call in a map target's key, before the receive.
func rCallMapKeyBeforeRecv() int {
	ch := make(chan int, 1)
	ch <- 7
	m := map[int]int{}
	m[rIdx(ch)] = <-ch
	return m[0]*10 + len(ch)
}

// R.11: a select clause's nil deref target — the receive commits, then the
// store panics (the channel is drained).
func rSelectNilDerefDrains() int {
	ch := make(chan int, 1)
	ch <- 7
	var p *int
	hit := rRecover(func() {
		select {
		case *p = <-ch:
		}
	})
	return hit*100 + len(ch)
}

// R.12: a select clause's out-of-range index target.
func rSelectOobDrains() int {
	ch := make(chan int, 1)
	ch <- 7
	xs := []int{0}
	hit := rRecover(func() {
		select {
		case xs[9] = <-ch:
		}
	})
	return hit*100 + len(ch)
}

// R.13: a select clause's nil-map target.
func rSelectNilMapDrains() int {
	ch := make(chan int, 1)
	ch <- 7
	var m map[int]int
	hit := rRecover(func() {
		select {
		case m[1] = <-ch:
		}
	})
	return hit*100 + len(ch)
}

// R.14: BUG-030's select twin — the map-element FIRST target's store lands
// before the nil second target's store panics.
func rSelectMapFirstStoreLands() int {
	ch := make(chan int, 1)
	ch <- 3
	m := map[int]int{}
	var okp *bool
	hit := rRecover(func() {
		select {
		case m[0], *okp = <-ch:
		}
	})
	return hit*1000 + m[0]*50/3
}

// R.15: a select clause with a blank element target.
func rSelectBlankElem() int {
	ch := make(chan int, 1)
	ch <- 7
	ok := false
	select {
	case _, ok = <-ch:
	}
	return b2i(ok)*10 + len(ch)
}

// R.16: a select clause with a blank ok target.
func rSelectBlankOk() int {
	ch := make(chan int, 1)
	ch <- 7
	v := 0
	select {
	case v, _ = <-ch:
	}
	return v*10 + len(ch)
}

// R.17: an interface-typed first target takes the temp-fallback lowering
// (boxing); its store lands before the second target's bounds panic.
func rSelectIfaceFallbackSecondOob() int {
	ch := make(chan int, 1)
	ch <- 7
	var iv any
	bs := []bool{}
	hit := rRecover(func() {
		select {
		case iv, bs[9] = <-ch:
		}
	})
	n := hit * 100
	if v, ok := iv.(int); ok {
		n += v
	}
	return n
}

// R.19: a closed channel's comma-ok receive into a NIL map element and an ok
// variable: the map store (first) panics, the ok store never happens.
func rClosedIntoNilMapOkUntouched() int {
	ch := make(chan int, 1)
	close(ch)
	var m map[int]int
	ok := true
	hit := rRecover(func() { m[1], ok = <-ch })
	return hit*100 + b2i(ok)*10
}

// R.23: a comma-ok receive into an index target inside a generic function.
func rGenRecv[T any](s []T, ch chan T) bool {
	var ok bool
	s[0], ok = <-ch
	return ok
}

func rGenericRecvIndex() int {
	ch := make(chan int, 1)
	ch <- 7
	s := []int{0}
	ok := rGenRecv(s, ch)
	return s[0]*10 + b2i(ok)
}

// R.26: BUG-022's select twin — a bad target of a BLOCKING receive clause is
// never evaluated: the select blocks (deadlock in the single-goroutine
// slice), it does not panic on the nil deref.
func rSelectBadTargetBlocks() int {
	ch := make(chan int)
	var p *int
	select {
	case *p = <-ch:
	}
	return 0
}

// R.28: a closed channel's single receive into a nil deref target — the
// (immediate) receive first, then the nil store panics.
func rClosedRecvNilDeref() int {
	ch := make(chan int, 1)
	close(ch)
	var p *int
	hit := rRecover(func() { *p = <-ch })
	return hit*100 + len(ch)
}

func main() {
	rNilMapRecvDrains()
}
