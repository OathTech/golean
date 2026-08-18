package main

// spec#Order_of_evaluation block Order_of_evaluation-1-8d2525f7: in
// the assignment y[f()], ok = g(z || h(), i()+x[j()], <-c), k(),
// "the function calls and communication happen in the order f(), h()
// (if z evaluates to false), i(), j(), <-c, g(), and k()". The order
// of those events relative to the evaluation/indexing of x, y, and z
// is not specified — so the observable is exactly the CALL trace,
// which the spec fixes completely (z is false here, so h runs).
//
// Two subjects: the verbatim form (raw <-c; traced events
// f,h,i,j,g,k, with the received value observable through g's
// result), and a variant wrapping the receive in a traced call at the
// same lexical slot, pinning the full 7-event order f,h,i,j,c,g,k —
// receive operations are ordered exactly like calls, left-to-right.
//
// Expected in both: y[1] == g(true, 30+7, 55) == 100+37+55 == 192,
// ok == true.

func evalOrderPieces(trace *string) (func() int, func() bool, func() int, func() int, func(bool, int, int) int, func() bool) {
	step := func(name string) {
		if *trace != "" {
			*trace += ","
		}
		*trace += name
	}
	f := func() int { step("f"); return 1 }
	h := func() bool { step("h"); return true }
	i := func() int { step("i"); return 30 }
	j := func() int { step("j"); return 1 }
	g := func(zh bool, ix int, cv int) int {
		step("g")
		if zh {
			return 100 + ix + cv
		}
		return ix + cv
	}
	k := func() bool { step("k"); return true }
	return f, h, i, j, g, k
}

// Verbatim form: raw <-c in argument position.
func evalOrderCallsVerbatim() (string, int, bool) {
	trace := ""
	f, h, i, j, g, k := evalOrderPieces(&trace)
	y := []int{0, 0, 0}
	x := []int{9, 7, 5}
	z := false
	c := make(chan int, 1)
	c <- 55

	var ok bool
	y[f()], ok = g(z || h(), i()+x[j()], <-c), k()
	return trace, y[1], ok
}

// Traced-receive variant: the communication slot lands in the trace.
func evalOrderCallsTracedRecv() (string, int, bool) {
	trace := ""
	f, h, i, j, g, k := evalOrderPieces(&trace)
	y := []int{0, 0, 0}
	x := []int{9, 7, 5}
	z := false
	c := make(chan int, 1)
	c <- 55
	recv := func() int {
		v := <-c
		if trace != "" {
			trace += ","
		}
		trace += "c"
		return v
	}

	var ok bool
	y[f()], ok = g(z || h(), i()+x[j()], recv()), k()
	return trace, y[1], ok
}

func main() {
	evalOrderCallsVerbatim()
}
