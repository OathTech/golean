package main

// Stage E of the evaluation-order model v2.1, family E3 (lane core/unseq-stage-e-0921,
// 2026-09-21): RECEIVES and METHOD CALLS as occurrences. A receive `<-ch` is an EVENT
// (spec#Order_of_evaluation orders «function calls, method calls, receive operations» in
// lexical order — the E1 edges; its communication happens once, the value lands in a
// predeclared binder), spec-unsequenced against the reads beside it; a method call on a
// CONCRETE receiver is an invocation whose receiver sub-evaluation is an occurrence (E14's
// sub-axis: a value receiver's COPY, a pointer operand's value, an addressable variable's
// address, the nil-asserting `&*p`). References: enumerate.py E3a/E3e (and X3/E3c/E3d for
// BUG-104's rows, which stay in builtins/e13-sibling-panic-order); the wires
// Tests/unseq-wire/e3recv.json + native-{e3recv,e3method}.json; gc's draws are call-first
// (the receive before the read; the receiver copy after the argument call).

type V struct{ n int }

func (v V) Plus(a int) int  { return v.n + a }
func (v *V) Bump() int      { v.n++; return v.n }
func wit(x int) int         { println("wit", x); return x }

// E3a: <-ch + x + mut(), x captured (mut: x = 2; the channel holds 1): the receive is E1-ordered
// before mut; the read of x before mut → 1 + 1 + 0 = 2, after → 1 + 2 + 0 = 3 (gc's). {2, 3}.
func recvVsRead() int {
	ch := make(chan int, 1)
	ch <- 1
	x := 1
	mut := func() int { x = 2; return 0 }
	return <-ch + x + mut()
}

// E3e: v.Plus(f()) with a VALUE receiver, f writing v.n = 10 and returning 5: the receiver
// COPY before f → 1 + 5 = 6, after → 10 + 5 = 15 (gc's). {6, 15}.
func valueRecvVsArgCall() int {
	v := V{n: 1}
	f := func() int { v.n = 10; return 5 }
	return v.Plus(f())
}

// A pointer-receiver call on a pointer operand beside a field read the call mutates:
// p.n + p.Bump() — the field read before the call → 1 + 2 = 3, after → 2 + 2 = 4 (gc's). {3, 4}.
func ptrRecvVsFieldRead() int {
	p := &V{n: 1}
	return p.n + p.Bump()
}

// A pointer-receiver call on an ADDRESSABLE variable (the implicit &v, a frozen address —
// no read) beside a slice read the call cannot touch: both orders agree — a strict control.
func addrRecvVsSliceRead() int {
	var v V
	s := []int{7}
	k := 0
	return s[k] + v.Bump()
}

// A receive beside an unrelated call: the receive is E1-ordered after the call (lexical
// order) and no read is unordered — a strict control (all edges forced).
func recvAfterCall() int {
	ch := make(chan int, 1)
	ch <- 1
	return wit(2) + <-ch
}

func main() {
	println(recvVsRead())
	println(valueRecvVsArgCall())
	println(ptrRecvVsFieldRead())
	println(addrRecvVsSliceRead())
	println(recvAfterCall())
}
