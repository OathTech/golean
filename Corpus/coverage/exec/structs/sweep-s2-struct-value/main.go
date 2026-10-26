package main

// Defect-neighbourhood campaign, shape S2 (conversions: a missing kernel arm or a
// value not retagged), lane sweep/s2-conversions, 2026-10-26: every row is an
// agreement with gc on a route no earlier row held (the matrix is on the member
// entries' Neighbourhood lines in docs/BUGS.md; the plan is
// docs/2026-10-27_defect-neighbourhood-campaign.md §4).
// The struct VALUE conversion B(a) (the kernel's retagged copy) on the routes
// BUG-134 swept for the POINTER: embedded and defined-type fields, fields
// holding references, a blank field, generic instantiations, defined over
// defined, literals, the returned value (the readout's type name), the box and
// its dynamic type, map keys, switch, parameters, channels, goroutines, value
// methods and method values, a call beside the conversion, a defined pointer
// type over a converted pointer, the conversion of a deref, an alias type,
// boxing inside a generic, operand kinds (map read, element, deref, receive), a
// method expression, and a struct type parameter instantiated at a named type.

type In struct{ V int }
type A struct{ X, Y int }
type B struct{ X, Y int }
type C B
type PB *B
type BB = B
type E1 struct {
	In
	N int
}
type E2 struct {
	In
	N int
}
type EP1 struct {
	*In
	N int
}
type EP2 struct {
	*In
	N int
}
type S1 struct {
	V In
	P *int
}
type S2 struct {
	V In
	P *int
}
type R1 struct {
	P   *int
	S   []int
	M   map[string]int
	F   func() int
	Ch  chan int
	I   any
	Arr [2]int
}
type R2 struct {
	P   *int
	S   []int
	M   map[string]int
	F   func() int
	Ch  chan int
	I   any
	Arr [2]int
}
type Bl1 struct {
	_ int
	X int
}
type Bl2 struct {
	_ int
	X int
}
type G[T any] struct {
	V T
	W int
}
type H[T any] struct {
	V T
	W int
}
type Outer struct {
	F B
	G []B
}
type TA struct{ X int }
type TB struct{ X int }

func (b B) Sum() int  { return b.X + b.Y }
func (c C) Diff() int { return c.X - c.Y }

func box[T any](x T) any { return x }

func convTP[T ~struct{ X int }](a TA) T { return T(a) }

func embeddedFields() int {
	e := E1{In{3}, 4}
	f := E2(e)
	f.V = 9
	return e.V*100 + f.V*10 + f.N
}

func definedFieldTypes() int {
	x := 5
	s := S1{In{2}, &x}
	t := S2(s)
	*t.P = 7
	t.V.V = 8
	return x*100 + s.V.V*10 + t.V.V
}

func refHoldingFields() int {
	x := 1
	r := R1{P: &x, S: []int{1, 2}, M: map[string]int{"a": 3}, F: func() int { return 4 }, Ch: make(chan int, 1), I: 5, Arr: [2]int{6, 7}}
	q := R2(r)
	q.S[0] = 10
	q.M["a"] = 30
	q.Arr[0] = 60
	q.Ch <- 8
	return *q.P + r.S[0] + r.M["a"] + q.F() + <-r.Ch + q.I.(int) + r.Arr[0] + q.Arr[0]
}

func blankField() int {
	a := Bl1{X: 3}
	b := Bl2(a)
	return b.X
}

func genericInstantiation() int {
	g := G[int]{V: 2, W: 3}
	h := H[int](g)
	gs := G[string]{V: "ab", W: 1}
	hs := H[string](gs)
	return h.V*100 + h.W*10 + len(hs.V) + hs.W
}

func definedOverDefined() int {
	a := A{1, 2}
	b := B(a)
	c := C(b)
	d := C(a)
	var i any = c
	r := 0
	switch i.(type) {
	case A:
		r = 1
	case B:
		r = 2
	case C:
		r = 3
	}
	return r*1000 + c.Diff()*100 + d.X*10 + B(c).Sum()
}

func inLiterals() int {
	a := A{1, 2}
	xs := []B{B(a), B(A{3, 4})}
	m := map[string]B{"k": B(a)}
	o := Outer{F: B(a), G: []B{B(a)}}
	keyed := map[B]int{B(a): 5}
	return xs[1].Y*1000 + m["k"].X*100 + o.F.Y*10 + keyed[B{1, 2}] + len(o.G)
}

func returned() B {
	a := A{5, 6}
	return B(a)
}

func boolToInt(b bool) int {
	if b {
		return 1
	}
	return 0
}

func boxed() (bool, bool, bool, int) {
	a := A{1, 2}
	var i any = B(a)
	_, isA := i.(A)
	bb, isB := i.(B)
	r := 0
	switch i.(type) {
	case A:
		r = 1
	case B:
		r = 2
	}
	return any(B(a)) == any(B{1, 2}), any(B(a)) == any(a), isA, r*10 + bb.X + boolToInt(isB)
}

func mapKeyAndSwitch() int {
	a := A{1, 2}
	m := map[B]int{{1, 2}: 7}
	r := m[B(a)]
	m[B(a)] = 8
	switch B(a) {
	case B{0, 0}:
		r += 100
	case B{1, 2}:
		r += 200
	}
	return r*10 + m[B{1, 2}]
}

func eqB(b B) bool { return b == B{1, 2} }

func paramAndChannel() int {
	a := A{1, 2}
	ch := make(chan B, 2)
	ch <- B(a)
	go func(b B) { ch <- b }(B(a))
	x := <-ch
	y := <-ch
	r := 0
	if eqB(B(a)) {
		r += 1
	}
	if x == y && x == (B{1, 2}) {
		r += 10
	}
	return r
}

func methodOnConversion() int {
	a := A{3, 4}
	s := B(a).Sum()
	mv := B(a).Sum
	a.X = 10
	e := B.Sum(B(a))
	return s*1000 + mv()*10 + e
}

var counter int

func bump() int { counter++; return counter }

func besideCall() int {
	a := A{1, 2}
	x := B(a).X + bump()
	y := bump() + B(a).Y
	return x*100 + y*10 + counter
}

func definedPointerOverConverted() int {
	a := A{1, 2}
	pb := PB((*B)(&a))
	r := 0
	if *pb == (B{1, 2}) {
		r += 1
	}
	pb.X = 5
	var i any = pb
	switch i.(type) {
	case *B:
		r += 10
	case PB:
		r += 20
	case *A:
		r += 40
	}
	return r*10 + a.X
}

func convOfDeref() int {
	a := A{1, 2}
	pb := (*B)(&a)
	c := C(*pb)
	d := C(*(*B)(&a))
	var i any = C(*pb)
	r := 0
	switch i.(type) {
	case A:
		r = 1
	case B:
		r = 2
	case C:
		r = 3
	}
	return r*100 + c.X*10 + d.Y
}

func aliasConversion() int {
	a := A{3, 4}
	b := BB(a)
	var i any = b
	r := 0
	switch i.(type) {
	case B:
		r = 1
	case A:
		r = 2
	}
	return r*10 + b.Sum()
}

func boxInGeneric() int {
	a := A{1, 2}
	i := box(B(a))
	j := box(a)
	r := 0
	if _, ok := i.(B); ok {
		r += 1
	}
	if _, ok := j.(A); ok {
		r += 10
	}
	if i == j {
		r += 100
	}
	if i == any(B{1, 2}) {
		r += 1000
	}
	return r
}

func embeddedPointerFieldValue() int {
	in := In{3}
	e := EP1{&in, 4}
	f := EP2(e)
	f.V = 9
	return in.V*100 + e.V*10 + f.N
}

func structArgInstantiation() int {
	g := G[A]{V: A{1, 2}, W: 3}
	h := H[A](g)
	var i any = h
	r := 0
	switch i.(type) {
	case G[A]:
		r = 1
	case H[A]:
		r = 2
	}
	return r*100 + h.V.Y*10 + h.W
}

func convOperandKinds() int {
	a := A{1, 2}
	m := map[string]A{"k": {3, 4}}
	as := []A{{5, 6}}
	pa := &a
	ch := make(chan A, 1)
	ch <- A{7, 8}
	b1 := B(m["k"])
	b2 := B(as[0])
	b3 := B(*pa)
	b4 := B(<-ch)
	return b1.Sum()*1000 + b2.Sum()*100 + b3.Sum()*10 + b4.Sum()/3
}

func methodExprConversion() int {
	f := (func(B) int)(B.Sum)
	a := A{2, 3}
	return f(B(a))
}

func structTypeParamConv() int {
	b := convTP[TB](TA{3})
	return b.X
}

func main() {}
