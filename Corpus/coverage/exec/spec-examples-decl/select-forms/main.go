package main

// spec#Select_statements block Select_statements-2-b1ed8c96: on entering a
// select, channel operands and send RHS are evaluated once in source order,
// but the LEFT-hand side of a receive assignment (a[f()]) is NOT evaluated
// unless that case is chosen — with c4 nil, f() never runs and nil a is
// never indexed. With c1 ready the c1 case is chosen over default; with all
// channels nil, default is chosen; select{} blocks forever (run-time
// deadlock). The block's print calls are realized as a recorder; its
// random-bit send loop is a nondeterministic segment, noted for the
// membership lane rather than pinned here.

var sLog string

var fCalls int

func f() int { fCalls++; return 0 }

func itoa(n int) string {
	if n < 10 {
		return string(rune('0' + n))
	}
	return itoa(n/10) + string(rune('0'+n%10))
}

func specSelect(ready bool) {
	var a []int
	var c1, c2, c3, c4 chan int
	if ready {
		c1 = make(chan int, 1)
		c1 <- 9
	}
	var i1, i2 int
	select {
	case i1 = <-c1:
		sLog += "received " + itoa(i1) + " from c1"
	case c2 <- i2:
		sLog += "sent " + itoa(i2) + " to c2"
	case i3, ok := (<-c3): // same as: i3, ok := <-c3
		if ok {
			sLog += "received " + itoa(i3) + " from c3"
		} else {
			sLog += "c3 is closed"
		}
	case a[f()] = <-c4:
		// same as: case t := <-c4; a[f()] = t
	default:
		sLog += "no communication"
	}
}

func selectReady() string {
	sLog = ""
	fCalls = 0
	specSelect(true)
	return sLog + "|f=" + itoa(fCalls) // f() never evaluated: c4 case not chosen
}

func selectDefault() string {
	sLog = ""
	fCalls = 0
	specSelect(false)
	return sLog + "|f=" + itoa(fCalls)
}

func selectBlockForever() int {
	select {} // block forever
}
