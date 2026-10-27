package main

// Sweep lane sweep/s13-binding (2026-10-27), shape S13: the implicit block of
// an if statement's init (spec#If_statements, #Blocks) — the variable in the
// else branch and down an else-if chain, shadowed in the body by a
// self-referential define, captured in the else branch, declared by a comma-ok
// map read. if/if-init-scope and scoping/for-init-scope, switch-init-shadow
// hold the plain forms. Expected = gc go1.26.5.

// F1
func ifInitElse() int {
	if x := 3; x > 10 {
		return -1
	} else {
		return x * 2 // 6
	}
}

// F2
func elseIfChain() int {
	if x := 1; x > 5 {
		return -1
	} else if y := x + 10; y > 50 {
		return -2
	} else {
		return x*100 + y // 111
	}
}

// F3
func ifInitBodySelfShadow() int {
	if x := 4; x > 0 {
		x := x * 2
		return x // 8
	}
	return -1
}

// F4
func ifInitCapturedInElse() int {
	var f func() int
	if x := 5; x > 10 {
		return -1
	} else {
		f = func() int { x++; return x }
	}
	return f() + f() // 13
}

// F8
func ifInitCommaokElse() int {
	m := map[int]int{1: 1}
	if v, ok := m[2]; ok {
		return -1
	} else {
		return v + 10 // 10
	}
}

func main() {
	println(ifInitElse(), elseIfChain(), ifInitBodySelfShadow(), ifInitCapturedInElse(), ifInitCommaokElse())
}
