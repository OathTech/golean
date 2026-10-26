package main

// BUG-134 (equality/identity review 2026-10-26, F1): the LOCAL SPACE of the
// whole-struct value through a struct-pointer conversion — the shapes this
// lane probed beside the review's p33 routes: a nested struct through the
// converted OUTER pointer, array and slice elements, a converted pointer
// stored and loaded later, a converted pointer to an embedded field, chained
// conversions, a struct holding pointers, a defined type over a defined
// struct, value-receiver methods and promoted methods through the alias,
// `range` over converted pointers, the interface dynamic-type rules, types
// differing only in tags, an embedded POINTER field, a pointer to the
// converted pointer, a converted pointer to an inner field of another type.
// Every row with a whole-value route born RED at the base (`stuck`);
// expected = gc.

type A struct{ X, Y int }
type B struct{ X, Y int }
type C B
type D A

func (b B) Sum() int  { return b.X + b.Y }
func (b *B) Ptr() int { return b.X }

type Summer interface{ Sum() int }

type In struct{ V int }

func (i In) Get() int   { return i.V }
func (i *In) Set(v int) { i.V = v }

type OA struct {
	I In
	N int
}
type OB struct {
	I In
	N int
}
type EA struct {
	In
	N int
}
type EB struct {
	In
	N int
}
type Outer struct {
	A
	N int
}
type Holder struct{ P *B }
type IA struct{ V int }
type IB struct{ V int }
type OIA struct {
	I IA
	N int
}
type PA struct {
	P *int
	Q *A
}
type PB struct {
	P *int
	Q *A
}
type TA struct {
	X int `json:"a"`
	Y int
}
type TB struct {
	X int `json:"b"`
	Y int
}
type PIn struct{ V int }
type EPA struct {
	*PIn
	N int
}
type EPB struct {
	*PIn
	N int
}

func b2i(b bool) int {
	if b {
		return 1
	}
	return 0
}

// A nested struct through the converted outer pointer: the inner field keeps
// its own type, the whole value takes `OB`.
func nestedOuter() int {
	o := OA{In{1}, 2}
	pb := (*OB)(&o)
	x := *pb
	r := x.I.V * 100
	if *pb == (OB{In{1}, 2}) {
		r += 10
	}
	if pb.I == (In{1}) {
		r += 1
	}
	return r
}

// A converted pointer to an array element.
func arrayElem() int {
	arr := [2]A{{1, 2}, {3, 4}}
	pb := (*B)(&arr[1])
	x := *pb
	return b2i(*pb == B{3, 4})*10 + x.X
}

// Converted pointers stored in a struct field, a map and a slice, loaded later.
func storedPointerLater() int {
	a := A{1, 2}
	h := Holder{P: (*B)(&a)}
	m := map[string]*B{"k": (*B)(&a)}
	s := []*B{(*B)(&a)}
	r := 0
	if *h.P == (B{1, 2}) {
		r += 100
	}
	if *m["k"] == (B{1, 2}) {
		r += 10
	}
	if *s[0] == (B{1, 2}) {
		r += 1
	}
	return r
}

// A converted pointer to an EMBEDDED field.
func embeddedField() int {
	o := Outer{A{1, 2}, 3}
	pb := (*B)(&o.A)
	x := *pb
	return b2i(*pb == B{1, 2})*100 + x.X + x.Y
}

// Chained conversions `(*C)((*B)(&a))`, and back.
func chained() int {
	a := A{1, 2}
	pc := (*C)((*B)(&a))
	pb := (*B)(pc)
	return b2i(*pc == C{1, 2})*100 + b2i(*pb == B{1, 2})*10 + b2i((*A)(pb) == &a)
}

// A struct holding pointers: the copy shares the pointees.
func structHoldingPointers() int {
	n := 5
	a := A{1, 2}
	pa := PA{&n, &a}
	pb := (*PB)(&pa)
	x := *pb
	*x.P = 9
	return b2i(*pb == PB{&n, &a})*1000 + b2i(pb.P == &n)*100 + b2i(*pb.Q == A{1, 2})*10 + n
}

// A defined type over a defined struct type (`type C B`, `type D A`): the
// boxes of `*pd` and `*pc` carry different dynamic types.
func definedOverDefined() int {
	a := A{1, 2}
	pc := (*C)(&a)
	pd := (*D)(&a)
	x := *pc
	return b2i(*pc == C{1, 2})*10000 + b2i(*pd == D{1, 2})*1000 + b2i(any(*pd) == any(D{1, 2}))*100 +
		b2i(any(*pd) == any(*pc))*10 + x.Y
}

// A value-receiver method through the converted pointer (the receiver is the
// whole value), beside a pointer-receiver one.
func valueReceiver() int {
	a := A{1, 2}
	pb := (*B)(&a)
	return pb.Sum()*10 + pb.Ptr()
}

// The same through interface boxes: a pointer box reads the cell at call
// time, a value box copied it.
func receiverViaBoxes() int {
	a := A{1, 2}
	pb := (*B)(&a)
	var i Summer = pb
	var j Summer = *pb
	a.X = 10
	return j.Sum()*100 + i.Sum()
}

// A method value bound through the alias, and a method expression applied to
// the dereferenced value.
func methodValue() int {
	a := A{1, 2}
	pb := (*B)(&a)
	f := pb.Sum
	g := B.Sum
	return f()*10 + g(*pb)
}

// Promoted methods through the converted OUTER pointer, then the whole value.
func promotedThroughOuter() int {
	o := EA{In{1}, 2}
	pb := (*EB)(&o)
	r := pb.Get()
	pb.Set(5)
	x := *pb
	return r*1000 + o.V*100 + x.Get()*10 + b2i(x == EB{In{5}, 2})
}

// `range` over converted pointers, each dereferenced whole.
func rangeLoad() int {
	as := []A{{1, 2}, {3, 4}}
	ps := []*B{(*B)(&as[0]), (*B)(&as[1])}
	sum := 0
	for _, p := range ps {
		x := *p
		sum += x.X
		if *p == (B{3, 4}) {
			sum += 100
		}
	}
	return sum
}

// The interface dynamic-type rules: `any(*pb)` is a `B` box, `any(*pa)` an
// `A` box — unequal, two map keys, the `B` clause of a type switch.
func ifaceDynamicType() int {
	a := A{1, 2}
	pb := (*B)(&a)
	pa := &a
	m := map[any]int{*pa: 1}
	m[*pb] = 2
	code := 0
	switch any(*pb).(type) {
	case A:
		code = 1
	case B:
		code = 2
	}
	return b2i(any(*pb) == any(*pa))*100000 + b2i(any(*pb) == any(B{1, 2}))*10000 + len(m)*1000 +
		m[A{1, 2}]*100 + m[B{1, 2}]*10 + code
}

// The box asserts as `B` only.
func boxAssertions() int {
	a := A{1, 2}
	pb := (*B)(&a)
	var e any = *pb
	_, okA := e.(A)
	_, okB := e.(B)
	return b2i(okA)*10 + b2i(okB)
}

// Types differing only in field tags (BUG-133's shape).
func tagOnly() int {
	a := TA{1, 2}
	pb := (*TB)(&a)
	x := *pb
	return b2i(*pb == TB{1, 2})*100 + x.Y*10 + b2i(any(*pb) == any(TB{1, 2}))
}

// An embedded POINTER field: the copy shares the pointee.
func embeddedPointerField() int {
	e := EPA{&PIn{1}, 2}
	pb := (*EPB)(&e)
	x := *pb
	x.PIn.V = 7
	return b2i(*pb == EPB{e.PIn, 2})*100 + pb.V*10 + e.V
}

// A pointer to the converted pointer, a converted `new`, a converted literal address.
func doublePointer() int {
	a := A{1, 2}
	pb := (*B)(&a)
	ppb := &pb
	pn := (*B)(new(A))
	pl := (*B)(&A{5, 6})
	r := 0
	if **ppb == (B{1, 2}) {
		r += 100
	}
	if *pn == (B{}) {
		r += 10
	}
	if *pl == (B{5, 6}) {
		r += 1
	}
	return r
}

// A converted pointer to an INNER field of another (compatible) type.
func innerField() bool {
	o := OIA{IA{1}, 2}
	pib := (*IB)(&o.I)
	return *pib == IB{1}
}

func main() {
	println(nestedOuter(), arrayElem(), storedPointerLater(), embeddedField(), chained(), structHoldingPointers(),
		definedOverDefined(), valueReceiver(), receiverViaBoxes(), methodValue())
	println(promotedThroughOuter(), rangeLoad(), ifaceDynamicType(), boxAssertions(), tagOnly(),
		embeddedPointerField(), doublePointer(), innerField())
}
