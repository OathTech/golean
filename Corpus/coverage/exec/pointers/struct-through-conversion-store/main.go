package main

// BUG-134 (equality/identity review 2026-10-26, F1): the WHOLE-STRUCT STORE
// through a struct-pointer conversion. `pb := (*B)(&a)` aliases the cell,
// which keeps its mint tag `A`; `*pb = B{…}` stores a `B` value INTO that cell
// and the original spelling observes it. Born RED at the base (every row
// `stuck`: «struct value type mismatch: expected main.A, got main.B» at the
// store); flips to PASS with the fix: the normalizer's struct arm retags a
// tag-compatible value at the DECLARED type before its shape checks
// (`retagStruct` in `normalizeValueForTyAt`, GoLean/GoCore/Ops.lean) — the
// cell keeps its mint tag, the value takes it.

type A struct{ X, Y int }
type B struct{ X, Y int }
type C struct{ X, Y int }
type In struct{ V int }

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

func b2i(b bool) int {
	if b {
		return 1
	}
	return 0
}

// p33g: the store is visible through the original spelling.
func storeThenOrig() bool {
	a := A{1, 2}
	pb := (*B)(&a)
	*pb = B{9, 9}
	return a == A{9, 9} && a.X == 9
}

// p33n: and through the alias.
func storeThenDerefEq() bool {
	a := A{1, 2}
	pb := (*B)(&a)
	*pb = B{9, 9}
	return *pb == B{9, 9}
}

// p33o: the cell's own value still boxes as `A` after the store.
func storeThenBoxTypeSwitch() int {
	a := A{1, 2}
	pb := (*B)(&a)
	*pb = B{9, 9}
	var i any = a
	code := 0
	switch v := i.(type) {
	case B:
		code = 2000 + v.X
	case A:
		code = 1000 + v.X
	}
	return code*100 + pb.X*10 + a.X
}

// p33o: boxed as `A`, equal to an `A` box.
func storeThenBoxEq() bool {
	a := A{1, 2}
	pb := (*B)(&a)
	*pb = B{9, 9}
	var i any = a
	return i == any(A{9, 9})
}

// p33q: fields and pointer identity after the store.
func storeThenFieldEq() int {
	a := A{1, 2}
	pb := (*B)(&a)
	*pb = B{9, 9}
	m := map[*int]int{&a.X: 1}
	return b2i(a.X == 9)*10000 + b2i(a.Y == 9)*1000 + b2i(pb.Y == 9)*100 + b2i(&a.X == &pb.X)*10 + m[&pb.X]
}

// p33r: a copy of the original after the store.
func storeThenCopyOrig() int {
	a := A{1, 2}
	pb := (*B)(&a)
	*pb = B{9, 9}
	c := a
	return c.X
}

// p33s: the store alone, between two prints.
func storeOnly() int {
	a := A{1, 2}
	pb := (*B)(&a)
	println("before")
	*pb = B{9, 9}
	println("after")
	return 1
}

// Swapped through two aliases in one assignment.
func swap() int {
	a := A{1, 2}
	c := A{3, 4}
	pb := (*B)(&a)
	pc := (*B)(&c)
	*pb, *pc = *pc, *pb
	return a.X*10 + c.X
}

// Copied alias to alias; the `B` copy is a value (its write stays local).
func copyBetweenAliases() int {
	a := A{1, 2}
	c := A{3, 4}
	pb := (*B)(&a)
	pc := (*B)(&c)
	*pb = *pc
	var b B = *pb
	b.X = 100
	return a.X*1000 + b.X
}

// Through a converted pointer stored in a struct field and a slice.
func throughStoredPointer() int {
	a := A{1, 2}
	h := Holder{P: (*B)(&a)}
	s := []*B{(*B)(&a)}
	*h.P = B{3, 4}
	return a.X*10 + b2i(*s[0] == B{3, 4})
}

// Through a converted pointer to an EMBEDDED field.
func embeddedField() int {
	o := Outer{A{1, 2}, 3}
	pb := (*B)(&o.A)
	*pb = B{5, 6}
	return o.X*100 + o.A.Y*10 + o.N
}

// Through a converted pointer to an array element.
func arrayElem() int {
	arr := [2]A{{1, 2}, {3, 4}}
	pb := (*B)(&arr[1])
	*pb = B{5, 6}
	return arr[1].X*10 + arr[1].Y
}

// Through a converted pointer to a slice element.
func sliceElem() int {
	as := []A{{1, 2}}
	pb := (*B)(&as[0])
	*pb = B{9, 9}
	return as[0].X*10 + b2i(*pb == B{9, 9})
}

// Through a CHAINED conversion `(*C)((*B)(&a))`.
func chained() int {
	a := A{1, 2}
	pc := (*C)((*B)(&a))
	*pc = C{7, 7}
	return a.X
}

// Through a pointer to the converted pointer.
func doublePointer() int {
	a := A{1, 2}
	pb := (*B)(&a)
	ppb := &pb
	**ppb = B{4, 4}
	return a.X
}

// Converted `new(A)` and a converted address of a literal.
func newAndLiteral() int {
	pn := (*B)(new(A))
	r := b2i(*pn == B{}) * 10
	*pn = B{1, 1}
	pl := (*B)(&A{5, 6})
	*pl = B{8, 8}
	return r + pn.X + pl.X*100
}

// Through a converted pointer to an INNER struct field of another type.
func innerField() int {
	o := OIA{IA{1}, 2}
	pib := (*IB)(&o.I)
	*pib = IB{5}
	return o.I.V*10 + b2i(o.I == IA{5})
}

// A struct holding pointers, stored whole through the alias.
func structHoldingPointers() bool {
	n := 5
	a := A{1, 2}
	pa := PA{&n, &a}
	pb := (*PB)(&pa)
	*pb = PB{nil, nil}
	return pa.P == nil && pa.Q == nil
}

// Types differing only in field tags (BUG-133's shape).
func tagOnly() int {
	a := TA{1, 2}
	pb := (*TB)(&a)
	*pb = TB{3, 4}
	x := *pb
	return a.X*10 + x.Y
}

// Stores through converted pointers taken in a loop.
func rangeStore() int {
	as := []A{{1, 2}, {3, 4}}
	ps := []*B{(*B)(&as[0]), (*B)(&as[1])}
	for i := range ps {
		*ps[i] = B{i + 7, i}
	}
	return as[0].X*10 + as[1].X
}

// Control (a leaf route, green at the base): a pointer-receiver method
// promoted through the converted outer pointer writes the embedded field.
func promotedSet() int {
	o := EA{In{1}, 2}
	pb := (*EB)(&o)
	pb.Set(5)
	return o.V
}

// A nested-field store (leaf, green at the base) then the whole store.
func nestedStore() int {
	o := OA{In{1}, 2}
	pb := (*OB)(&o)
	pb.I = In{5}
	r := o.I.V
	*pb = OB{In{7}, 8}
	return r*100 + o.I.V*10 + o.N
}

func main() {
	println(storeThenOrig(), storeThenDerefEq(), storeThenBoxTypeSwitch(), storeThenBoxEq(), storeThenFieldEq(),
		storeThenCopyOrig(), storeOnly(), swap(), copyBetweenAliases(), throughStoredPointer(), embeddedField())
	println(arrayElem(), sliceElem(), chained(), doublePointer(), newAndLiteral(), innerField(),
		structHoldingPointers(), tagOnly(), rangeStore(), promotedSet(), nestedStore())
}
