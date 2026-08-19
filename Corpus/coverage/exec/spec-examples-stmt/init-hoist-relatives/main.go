package main

// The BUG-058 NON-affected relatives, pinned GREEN so the if-init fix
// cannot regress them silently (bug-fix arc slice 1, 2026-08-19).
//
// spec#For_statements / spec#Expression_switches / spec#Type_switches:
// each of these statements also admits an init statement that "executes
// before the expression is evaluated". The P3 delta-review corroborated
// structurally that their lowerings already keep the condition/tag hoists
// inside the init's scope — emitFor routes condition hoists into
// `condPre` INSIDE the loop node, emitSwitch/emitTypeSwitch append tag
// hoists after the init — but "probed clean once" is not a guardrail, so
// each shape gets a row here with `go run`'s answer.

// forInitCondOrder: a runs once (init), b runs at every test. Go:
// a(1), b(2) -> 0<1 true, body, i=1, b(2) -> 1<1 false -> 122.
func forInitCondOrder() int {
	order := 0
	a := func() int { order = order*10 + 1; return 0 }
	b := func() int { order = order*10 + 2; return 1 }
	sum := 0
	for i := a(); i < b(); i++ {
		sum += i
	}
	return order*10 + sum
}

// switchInitTagOrder: init a, then the tag expression's call b.
func switchInitTagOrder() int {
	order := 0
	a := func() int { order = order*10 + 1; return 1 }
	b := func() int { order = order*10 + 2; return 1 }
	switch x := a(); b() + x {
	case 2:
		order = order*10 + 5
	default:
		order = order*10 + 6
	}
	return order
}

// typeSwitchInitOrder: init a, then the type-switch tag's call b, which
// READS the init-declared x (the position that goes stuck for `if`).
func typeSwitchInitOrder() int {
	order := 0
	a := func() int { order = order*10 + 1; return 3 }
	b := func(n int) any { order = order*10 + 2; return n }
	switch v := b(a()).(type) {
	case int:
		order = order*10 + v
	default:
		order = order*10 + 9
	}
	return order
}

// typeSwitchInitReadsInit: the init-declared variable used INSIDE the
// tag expression's call — the exact if-init failure position.
func typeSwitchInitReadsInit() int {
	order := 0
	a := func() int { order = order*10 + 1; return 3 }
	b := func(n int) any { order = order*10 + 2; return n }
	switch x := a(); v := b(x).(type) {
	case int:
		order = order*10 + v
	default:
		order = order*10 + 9
	}
	return order
}

// switchInitTagReadsInit: same for an expression switch.
func switchInitTagReadsInit() int {
	order := 0
	a := func() int { order = order*10 + 1; return 3 }
	b := func(n int) int { order = order*10 + 2; return n }
	switch x := a(); b(x) {
	case 3:
		order = order*10 + 5
	default:
		order = order*10 + 6
	}
	return order
}

// forInitCondReadsInit: the loop condition's call reads the loop
// variable declared by the init.
func forInitCondReadsInit() int {
	order := 0
	a := func() int { order = order*10 + 1; return 0 }
	b := func(n int) int { order = order*10 + 2; return n + 1 }
	sum := 0
	for i := a(); i < b(i); i++ {
		sum += i
		if i > 1 {
			break
		}
	}
	return order*100 + sum
}
