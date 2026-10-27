package main

// Sweep lane sweep/s13-binding (2026-10-27), shape S13: capture BY REFERENCE
// (emitFuncLit's lambda lifting: pointers to the captured cells) at the shapes
// functions/closure-* do not hold — a capture before the first assignment,
// the address identity through the capture, a field and an array element
// written through a captured aggregate, three levels with the middle level
// shadowing, the literal's own named result shadowing a capture, a deferred
// closure reading the final value, a returned closure whose capture moves
// between calls, a closure stored in a package-level variable. Expected = gc.

type S struct{ a, b int }

var stored func() int

// H2
func captureBeforeAssign() int {
	var x int
	f := func() int { return x }
	before := f()
	x = 5
	return before*10 + f() // 5
}

// H7
func addrIdentityThroughCapture() bool {
	x := 1
	p := &x
	f := func() *int { return &x }
	return p == f() // true
}

// H8
func fieldWrite() int {
	s := S{1, 2}
	f := func() { s.a = 10 }
	f()
	return s.a*10 + s.b // 102
}

// H9
func arrayElemWrite() int {
	a := [3]int{1, 2, 3}
	f := func(i, v int) { a[i] = v }
	f(1, 20)
	return a[0] + a[1] + a[2] // 24
}

// H10
func threeLevelsMiddleShadow() int {
	x := 1
	f := func() int {
		x := 2
		g := func() int { x++; return x }
		r := g() // sequenced: `g() + x` would be a spec-unordered pair (S8's envelope)
		return r + x // 6
	}
	return f()*10 + x // 61
}

// H15
func litResultShadowsCapture() int {
	x := 1
	f := func() (x int) { x = 5; return }
	return f() + x // 6
}

// H17
func deferSeesFinal() (r int) {
	x := 1
	defer func() { r = x }()
	x = 9
	return 0 // 9
}

// H18
func returnedClosureMutatedBetween() int {
	x := 1
	mk := func() func() int { return func() int { return x } }
	g := mk()
	a := g()
	x = 7
	return a*10 + g() // 17
}

// H23
func storedInGlobal() int {
	x := 3
	stored = func() int { x++; return x }
	return stored() + stored() // 9
}

func main() {
	println(captureBeforeAssign(), addrIdentityThroughCapture(), fieldWrite(), arrayElemWrite(),
		threeLevelsMiddleShadow(), litResultShadowsCapture(), deferSeesFinal(), returnedClosureMutatedBetween(),
		storedInGlobal())
}
