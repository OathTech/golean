package main

// spec#If_statements + spec#Order_of_evaluation: the if statement's init
// "executes before the expression is evaluated", and within the condition
// the usual operand order applies. These are the BUG-058 wrong-answer
// guardrails (P3 audit B1): the frontend's short-circuit hoisting emits
// the condition's desugar block BEFORE the if, outside the init's scope,
// so a call in the condition's right operand runs before the init.

// condCallAfterInit: go runs a (init) then b (condition) -> order 12.
// The defective lowering runs b first -> 21.
func condCallAfterInit() int {
	order := 0
	a := func() int { order = order*10 + 1; return 1 }
	b := func() int { order = order*10 + 2; return 1 }
	if x := a(); b() == x {
		order = order * 1
	}
	return order
}

// initPanicFirst: the init's s[0] panics before b can run; go never runs
// b (returns 1); the defective lowering runs b first (returns 21).
func initPanicFirst() (out int) {
	ran := 0
	defer func() {
		if recover() != nil {
			out = ran*10 + 1
		}
	}()
	var s []int
	b := func() int { ran = 2; return 0 }
	if x := s[0]; b() == x {
		ran = ran * 1
	}
	return ran
}

// ---- BUG-058 edge enumeration (bug-fix arc slice 1, 2026-08-19) ----
// The trigger is "an if with an init statement plus ANY hoisting
// call/alloc in the condition"; these rows walk the positions that
// combination can occupy. Every expectation below is `go run`'s.

// elseIfChainOrder: an `else if` has its OWN init and its own condition
// call. Go: a (init 1), b (cond 2, false), c (else-if init 3), d
// (else-if cond 4, true) -> 12348. The defect hoists each condition's
// call ahead of its own init INDEPENDENTLY at both links of the chain
// (the else accumulator is already scoped, so the else-if's call lands
// inside the else branch but still before its init) -> 21438.
func elseIfChainOrder() int {
	order := 0
	a := func() int { order = order*10 + 1; return 0 }
	b := func() int { order = order*10 + 2; return 9 }
	c := func() int { order = order*10 + 3; return 5 }
	d := func() int { order = order*10 + 4; return 5 }
	if x := a(); b() == x {
		order = order*10 + 7
	} else if y := c(); d() == y {
		order = order*10 + 8
	}
	return order
}

// ifInitInFuncLit: the same shape inside a function literal — the
// literal's body is emitted by the same statement-list machinery, so the
// defect travels into closures (the P3 delta-review's F-3 widening).
func ifInitInFuncLit() int {
	order := 0
	f := func() int {
		a := func() int { order = order*10 + 1; return 1 }
		b := func() int { order = order*10 + 2; return 1 }
		if x := a(); b() == x {
			order = order*10 + 5
		}
		return order
	}
	return f()
}

// nestedIfInit: an if-with-init inside an if-with-init. Go runs
// a,b (outer) then c,d (inner) -> 12349; the defect inverts each level
// independently -> 21439.
func nestedIfInit() int {
	order := 0
	a := func() int { order = order*10 + 1; return 1 }
	b := func() int { order = order*10 + 2; return 1 }
	c := func() int { order = order*10 + 3; return 1 }
	d := func() int { order = order*10 + 4; return 1 }
	if x := a(); b() == x {
		if y := c(); d() == y {
			order = order*10 + 9
		}
	}
	return order
}

func dbl(v int) int { return v * 2 }

// condHoistReadsInit: mode (1) of the entry — the hoisted condition call
// READS the init-declared variable, so lifting it out of the init's
// scope leaves the reference unbound (machine stuck) rather than merely
// mis-ordered. No short-circuit operator and no closure involved.
func condHoistReadsInit() int {
	if x := 21; dbl(x) == 42 {
		return 1
	}
	return 0
}

// condPanicAfterInit: the ordering mirror of initPanicFirst — the init
// SUCCEEDS (observably) and the condition's hoisted call panics. Go runs
// a then boom -> ran 32 -> 321; the defect runs boom first -> 21.
func condPanicAfterInit() (out int) {
	ran := 0
	defer func() {
		if recover() != nil {
			out = ran*10 + 1
		}
	}()
	var s []int
	a := func() int { ran = ran*10 + 3; return 0 }
	boom := func() int { ran = ran*10 + 2; return s[0] }
	if x := a(); boom() == x {
		ran = 0
	}
	return ran
}

// ---- the raft shape (integration) ----

type progress struct{ n int }

func (p progress) active() bool { return p.n > 5 }

func big(v int) bool { return v > 5 }

// commaOkShortCircuit: `if v, ok := m[k]; ok && f(v)` — one of the most
// common shapes in real Go and in deps/raft. The short-circuit RHS
// normalizes to a hoisted `if $c { $c = f(v) }` block that reads BOTH
// init-declared names, so the defect makes it stuck; the present-key and
// absent-key arms together pin that the guard still short-circuits.
func commaOkShortCircuit() int {
	m := map[string]int{"a": 7, "b": 2}
	total := 0
	if v, ok := m["a"]; ok && big(v) {
		total += 1
	}
	if v, ok := m["b"]; ok && big(v) {
		total += 10
	}
	if v, ok := m["c"]; ok && big(v) {
		total += 100
	}
	return total
}

// commaOkMethodShortCircuit: the same shape with a METHOD call in the
// right operand, which is what raft actually writes
// (`if pr, ok := m[id]; ok && pr.IsPaused()`).
func commaOkMethodShortCircuit() int {
	m := map[int]progress{1: {n: 7}, 2: {n: 2}}
	total := 0
	if pr, ok := m[1]; ok && pr.active() {
		total += 1
	}
	if pr, ok := m[2]; ok && pr.active() {
		total += 10
	}
	if pr, ok := m[3]; ok && pr.active() {
		total += 100
	}
	return total
}
