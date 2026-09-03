// noodler probes — spec#Order_of_evaluation: "all function calls, method
// calls, receive operations, and binary logical operations are evaluated
// in lexical left-to-right order". Each subject records the call order
// in a trace and returns it as a base-10 digit string.
package main

var tr []int

func t(n int) int { tr = append(tr, n); return n }

func digits() int {
	r := 0
	for _, d := range tr {
		r = r*10 + d
	}
	tr = nil
	return r
}

// Slice literal elements.
func sliceLiteralOrder() (int, int) {
	s := []int{t(1), t(2), t(3)}
	return digits(), s[2]
}

// Map literal: key then value, entry by entry.
func mapLiteralOrder() int {
	m := map[int]int{t(1): t(2), t(3): t(4)}
	return digits()*10 + len(m)
}

// Keyed struct literal in reverse field order: source order wins.
type pair struct{ a, b int }

func structLiteralReverseKeys() int {
	p := pair{b: t(1), a: t(2)}
	return digits()*100 + p.a*10 + p.b
}

// Function value before its arguments.
func pick() func(int) int { t(1); return func(x int) int { return x } }

func funcValueBeforeArgs() int {
	pick()(t(2))
	return digits()
}

// Method call: receiver expression before arguments.
type obj struct{}

func (obj) m(x int) int { return x }

func mk() obj { t(1); return obj{} }

func receiverBeforeArgs() int {
	mk().m(t(2))
	return digits()
}

// Binary operators: left-to-right across precedence levels.
func binaryOperatorCalls() int {
	_ = t(1) + t(2)*t(3) - t(4)
	return digits()
}

// Tuple assignment RHS then return expression order.
func tupleAssignAndReturn() (int, int) {
	var a, b int
	a, b = t(1), t(2)
	d1 := digits()
	f := func() (int, int) { return t(3), t(4) }
	f()
	return d1*100 + a + b, digits()
}

// defer arguments at defer time, in order.
func deferArgsOrder() int {
	func() {
		defer func(int, int) {}(t(1), t(2))
		t(3)
	}()
	return digits()
}

// Index operand call before RHS call: s[f()] = g().
func indexBeforeRHS() int {
	s := make([]int, 3)
	s[t(1)] = t(2)
	return digits()*10 + s[1]
}

// *p() = f(): pointer-producing call first.
func derefCallBeforeRHS() int {
	x := 0
	p := func() *int { t(1); return &x }
	*p() = t(2)
	return digits()*10 + x
}

// Map index assignment m[f()] = g().
func mapIndexBeforeRHS() int {
	m := map[int]int{}
	m[t(1)] = t(2)
	return digits()*10 + m[1]
}

// Receive vs call in one RHS list: lexical order.
func receiveBeforeCall() int {
	c := make(chan int, 1)
	c <- 5
	var a, b int
	a, b = <-c, t(1)
	tr = append(tr, a)
	return digits()*10 + b
}

// Channel send: channel expression then value.
func sendOperandOrder() int {
	c := make(chan int, 1)
	ch := func() chan int { t(1); return c }
	ch() <- t(2)
	return digits()*10 + <-c
}

// append(f(), g()).
func appendArgsOrder() int {
	s := func() []int { t(1); return nil }
	r := append(s(), t(2))
	return digits()*10 + len(r)
}

// Conversion of a call, and comparison operands.
func conversionAndComparison() int {
	_ = int64(t(1)) == int64(t(2))
	_ = t(3) < t(4)
	return digits()
}

// String concatenation of calls.
func stringConcatOrder() (string, int) {
	f := func(n int, s string) string { t(n); return s }
	r := f(1, "a") + f(2, "b") + f(3, "c")
	return r, digits()
}

// Method value: the receiver is evaluated once at creation.
func methodValueReceiverOnce() int {
	f := mk().m
	f(t(2))
	f(t(3))
	return digits()
}

// Range over a call result: the call happens once.
func rangeCallOnce() int {
	g := func() []int { t(1); return []int{5, 6} }
	sum := 0
	for _, v := range g() {
		sum += v
	}
	return digits()*100 + sum
}

// Nested calls: inner arguments before outer call; sibling order.
func nestedCalls() int {
	id := func(x int) int { return x }
	_ = id(t(1)+id(t(2))) + id(t(3))
	return digits()
}

// Logical operators short-circuit in order.
func logicalShortCircuit() int {
	b := func(n int, v bool) bool { t(n); return v }
	_ = b(1, false) && b(2, true)
	_ = b(3, true) || b(4, true)
	_ = b(5, true) && b(6, false) || b(7, true)
	return digits()
}

// Switch tag then case expressions until the first match.
func switchTagAndCases() int {
	switch t(1) {
	case t(2):
	case t(1):
	case t(3):
	}
	return digits()
}

// Composite literal of pointers with elided types and calls.
func elidedPointerLiteralOrder() int {
	ps := []*pair{{t(1), t(2)}, {t(3), t(4)}}
	return digits()*10 + ps[1].b - ps[0].a
}

func main() {}
