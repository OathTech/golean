package main

// Stage E5 of the evaluation-order model v2.1, family E5d (lane core/unseq-stage-e5-0922,
// 2026-09-22): THE ADDRESS OF A VARIABLE as an operand. `&x` is an ADDRESS FORMATION
// (spec#Address_operators): it reads nothing and cannot fail (its operand is a variable, not a
// dereference), so it is NO occurrence of the graph — it is carried as the frontend's own address
// spelling (`ref x`, `globaladdr`) where an already-evaluated value is consumed: a call argument, an
// allocation payload, a plain local's stored value, a return operand. The READS of the address-taken
// variable beside the call that receives the address are the occurrences — spec-unsequenced against
// it. References: enumerate.py E5d1–E5d3; the wires Tests/unseq-wire/{e5daddr,e5dlit}.json + native.

type PT struct{ p *int }

var g = 1

// use writes 7 through the pointer and returns 1.
func use(p *int) int {
	*p = 7
	return 1
}

// peek reads through the pointer.
func peek(p *int) int { return *p }

// use(&x) + x: &x an argument (no read); x's read is unordered against use (which writes *p = 7):
// before 1 + 1 = 2, after 7 + 1 = 8. {2, 8}.
func addrArgVsRead() int {
	x := 1
	return use(&x) + x
}

// *(&PT{p: &x}).p + m() with m writing x = 10 (returns 5): &x the struct literal's payload (no read);
// the literal an allocate body without an E1 edge; the dereference through the fresh pointer's field
// reads x — before m 1 + 5 = 6, after 10 + 5 = 15. {6, 15}.
func addrPayloadVsCall() int {
	x := 1
	m := func() int { x = 10; return 5 }
	return *(&PT{p: &x}).p + m()
}

// p, y = &x, use(&x)+x — a tuple with NO planned target: the stored address rides the completion (no
// occurrence); y's sweep is addrArgVsRead's {2, 8}; *p reads x = 7 after the sweep: 72 or 78. {72, 78}.
func addrStoredVsRead() int {
	x := 1
	var p *int
	var y int
	p, y = &x, use(&x)+x
	return *p*10 + y
}

// use(&g) + g on a PACKAGE-LEVEL variable: &g is the seeded cell's address (`globaladdr`, no read); g's
// read (`deref(globaladdr)`, E1) is unordered against use — before 2, after 8. {2, 8}.
func addrGlobalArgVsRead() int {
	g = 1
	return use(&g) + g
}

// STRICT CONTROL: peek(&x) + x with peek only READING through the pointer: both orders 1 + 1 = 2 — the
// graph's two picks agree (the address itself contributes no read and no failure).
func addrArgPureControl() int {
	x := 1
	return peek(&x) + x
}
