// noodler probes — spec#Order_of_evaluation's UNSPECIFIED axes: a
// non-call operand (index read, variable read, receiver copy) beside a
// call that mutates what it reads. The machine's ANF realization is
// call-first (latitude inventory E12/E13/E14); gc's realization is what
// these rows record. A strict row here pins ONE member of the plausible
// envelope — a mismatch is observed-not-modeled, not a spec violation.
package main

// Slice literal: element a[i] beside f() mutating a[i].
func sliceLiteralIndexVsCall() int {
	a := []int{1, 2}
	f := func() int { a[0] = 100; return 5 }
	s := []int{a[0], f()}
	return s[0]*10 + s[1]
}

// Struct literal: field from a variable beside a call mutating it.
func structLiteralVarVsCall() int {
	type P struct{ x, y int }
	v := 1
	f := func() int { v = 100; return 5 }
	p := P{v, f()}
	return p.x*10 + p.y
}

// Map literal: key is an index read, value is a call mutating the index.
func mapLiteralKeyVsCall() int {
	a := []int{1, 2}
	f := func() int { a[0] = 7; return 5 }
	m := map[int]int{a[0]: f()}
	k1, ok1 := m[1]
	k7, ok7 := m[7]
	r := 0
	if ok1 {
		r += k1
	}
	if ok7 {
		r += k7 * 10
	}
	return r
}

// Value receiver beside an argument call that mutates the receiver.
type V struct{ n int }

func (v V) Plus(x int) int { return v.n + x }

func receiverVsArgCall() int {
	v := V{1}
	f := func() int { v.n = 100; return 5 }
	return v.Plus(f())
}

// Plain call arguments: index read beside a mutating call.
func argsIndexVsCall() int {
	a := []int{1, 2}
	f := func() int { a[0] = 100; return 5 }
	g := func(x, y int) int { return x*10 + y }
	return g(a[0], f())
}

// Variable read beside a mutating call in string concatenation.
func concatVarVsCall() string {
	s := "a"
	f := func() string { s = "z"; return "b" }
	return s + f()
}

// Conversion of an index read beside a mutating call.
func conversionIndexVsCall() int64 {
	a := []int32{1}
	f := func() int64 { a[0] = 100; return 5 }
	return int64(a[0]) + f()
}

// Deref read beside a call that redirects the pointer.
func derefVsCall() int {
	x, y := 1, 2
	p := &x
	f := func() int { p = &y; return 10 }
	return *p + f()
}

// Two index reads with a call between them.
func indexCallIndex() int {
	a := []int{1, 2, 3}
	f := func() int { a[0], a[2] = 100, 300; return 0 }
	return a[0] + f() + a[2]
}

// Return statement operands: variable beside mutating call.
func returnOperands() (int, int) {
	v := 1
	f := func() int { v = 100; return 5 }
	return v, f()
}

// Channel send: the value operand read beside a call in the channel
// operand position.
func sendValueVsChannelCall() int {
	c := make(chan int, 1)
	v := 1
	pick := func() chan int { v = 100; return c }
	pick() <- v
	return <-c
}

// Assignment RHS list: index read then a call that mutates it, then the
// index again.
func rhsListIndexCallIndex() (int, int, int) {
	a := []int{1, 2}
	f := func() int { a[0] = 9; return 5 }
	x, y, z := a[0], f(), a[0]
	return x, y, z
}

func main() {}
