package main

// F20 frontier enumeration (slice 6; triage row F20): the ASSIGNMENT
// form of the range clause with NON-IDENTIFIER targets. spec#For_range:
// "The iteration variables may be declared by the 'range' clause …
// or they may be pre-declared" — in the assignment form the left
// operands are ordinary assignment targets, re-evaluated PER ITERATION
// (spec#Assignment_statements two-phase). The frontend's range lowering
// binds iteration variables by identifier and refuses everything else:
// emit.go "range assignment to non-identifier target (operands
// evaluate per iteration)". The spec's own subtle shape
// (for i, x[i] = range x) is pinned at
// spec-examples-decl/assign-tuple-order/range-assign; these rows
// enumerate the remaining target kinds so the lift's edge set exists
// before the lift.
//
// map-elem-target is the order-observing row: each iteration's index
// expression m[k] is evaluated with the PREVIOUS iteration's k
// (phase 1 before the assignment lands), so both values pile onto
// m[0] and k finishes at 1 — go run: 161 (k=1, m[0]=6, len(m)=1).

type rafPair struct{ k, v int }

func rafFieldTarget() int {
	var p rafPair
	for p.k, p.v = range []int{7, 8} {
	}
	return p.k*10 + p.v // 18
}

func rafDerefTarget() int {
	var k, v int
	kp, vp := &k, &v
	for *kp, *vp = range []int{7, 8} {
	}
	return k*10 + v // 18
}

func rafMapElemTarget() int {
	m := map[int]int{}
	k := 0
	for k, m[k] = range []int{5, 6} {
	}
	return k*100 + m[0]*10 + len(m) // 161
}

func main() {
	rafFieldTarget()
	rafDerefTarget()
	rafMapElemTarget()
}
