package main

// BUG-134 (equality/identity review 2026-10-26, F1): the WHOLE-STRUCT VALUE
// reached through a struct-pointer conversion. `pb := (*B)(&a)` for two
// struct types with identical underlying types aliases the cell, which keeps
// its mint tag `A`; Go gives `*pb` the type `B`, so every value route —
// `==`, `!=`, assignment, boxing (dynamic type `B`), map keys, `switch`,
// parameter binding, type assertion of the box, the returned value's type
// name — prints gc's answer. Born RED at the base (every row `stuck` with
// «struct equality / value type mismatch»); flips to PASS with the fix: the
// `.deref` read retags the loaded value at the pointee's static type when the
// two tags are tag-compatible (`derefRetag`, GoLean/GoCore/Ops.lean).

type A struct{ X, Y int }
type B struct{ X, Y int }
type In struct{ V int }
type OA struct {
	I In
	N int
}
type OB struct {
	I In
	N int
}
type W struct{ F B }

func b2i(b bool) int {
	if b {
		return 1
	}
	return 0
}

// p33a: `*pb == B{…}`.
func eqLiteral() bool {
	a := A{1, 2}
	pb := (*B)(&a)
	return *pb == B{1, 2}
}

// p33b: the deref on the right.
func eqRight() bool {
	a := A{1, 2}
	pb := (*B)(&a)
	return B{1, 2} == *pb
}

// p33c: assigned to a `B` variable, then compared and projected.
func assignThenEq() bool {
	a := A{1, 2}
	pb := (*B)(&a)
	x := *pb
	return x == B{1, 2} && x.X == 1
}

// p33d: boxed, the dynamic type is `B`.
func boxedSameType() bool {
	a := A{1, 2}
	pb := (*B)(&a)
	return any(*pb) == any(B{1, 2})
}

// p33d: Go's dynamic-type rule — `B` vs `A` boxes are unequal.
func boxedTypeDiffers() bool {
	a := A{1, 2}
	pb := (*B)(&a)
	return any(*pb) == any(A{1, 2})
}

// p33e: a map key at `B` (lookup, then insert overwriting the entry).
func mapKey() int {
	a := A{1, 2}
	pb := (*B)(&a)
	m := map[B]int{{1, 2}: 1}
	r := m[*pb]*10 + len(m)
	m[*pb] = 2
	return r*100 + m[B{1, 2}]*10 + len(m)
}

// p33f: an expression switch on the value.
func switchValue() string {
	a := A{1, 2}
	pb := (*B)(&a)
	switch *pb {
	case B{1, 2}:
		return "matched"
	}
	return "default"
}

// p33i: a nested struct field keeps its own (identical) type.
func nestedField() bool {
	o := OA{In{1}, 2}
	pb := (*OB)(&o)
	return pb.I == In{1} && *pb == OB{In{1}, 2}
}

func eqB(b B) bool { return b == B{1, 2} }

// p33j: passed as a `B` parameter.
func param() bool {
	a := A{1, 2}
	pb := (*B)(&a)
	return eqB(*pb)
}

// p33l: `!=`, and the pointer identities beside it.
func neqAndPtrEq() int {
	a := A{1, 2}
	pb := (*B)(&a)
	return b2i(*pb != B{1, 3})*100 + b2i(pb == (*B)(&a))*10 + b2i((*A)(pb) == &a)
}

// p33m: the converted pointer to a slice element.
func sliceElem() bool {
	as := []A{{1, 2}}
	pb := (*B)(&as[0])
	return *pb == B{1, 2}
}

// p33p: the box asserts as `B`, not as `A`.
func boxAssert() int {
	a := A{1, 2}
	pb := (*B)(&a)
	var i any = *pb
	_, isA := i.(A)
	v, isB := i.(B)
	return b2i(isA)*100 + b2i(isB)*10 + v.X
}

// p33p: the type switch takes the `B` clause.
func typeSwitch() string {
	a := A{1, 2}
	pb := (*B)(&a)
	var i any = *pb
	switch i.(type) {
	case A:
		return "A"
	case B:
		return "B"
	}
	return "none"
}

// The value RETURNED to the observer: its type name is `B` (the readout
// renders the tag).
func returned() B {
	a := A{1, 2}
	pb := (*B)(&a)
	return *pb
}

func eq[T comparable](x, y T) bool { return x == y }

// Compared inside a generic function instantiated at `B`.
func genericEq() int {
	a := A{1, 2}
	pb := (*B)(&a)
	return b2i(eq(*pb, B{1, 2}))*100 + b2i(eq(B{1, 2}, *pb))*10 + b2i(eq(*pb, *pb))
}

// Returned from a closure capturing the converted pointer.
func closure() bool {
	a := A{1, 2}
	pb := (*B)(&a)
	f := func() B { return *pb }
	return f() == B{1, 2}
}

// Passed as a goroutine argument and sent on a `chan B`.
func goroutineArg() bool {
	a := A{1, 2}
	pb := (*B)(&a)
	ch := make(chan B, 1)
	go func(b B) { ch <- b }(*pb)
	return (<-ch) == B{1, 2}
}

// Inside composite literals and `append` at element type `B`.
func composites() int {
	a := A{1, 2}
	pb := (*B)(&a)
	arr := [1]B{*pb}
	sl := []B{*pb, *pb}
	st := W{*pb}
	m := map[int]B{1: *pb}
	sl = append(sl, *pb)
	return b2i(arr[0] == B{1, 2})*10000 + sl[1].Y*1000 + b2i(st.F == B{1, 2})*100 +
		m[1].X*10 + b2i(len(sl) == 3 && sl[2] == B{1, 2})
}

func two(b B) (B, B) { return b, b }

func many(bs ...B) int {
	n := 0
	for _, b := range bs {
		n += b.X
	}
	return n
}

// Multi-result and variadic binding at `B`.
func multiAndVariadic() int {
	a := A{1, 2}
	pb := (*B)(&a)
	x, y := two(*pb)
	return b2i(x == y)*10 + many(*pb, *pb, B{1, 2})
}

// The asserted copy is a COPY: writing it leaves the cell alone.
func boxThenCopy() int {
	a := A{1, 2}
	pb := (*B)(&a)
	var i any = *pb
	b := i.(B)
	b.X = 9
	return a.X*10 + b.X
}

func main() {
	println(eqLiteral(), eqRight(), assignThenEq(), boxedSameType(), boxedTypeDiffers(), mapKey(),
		switchValue(), nestedField(), param(), neqAndPtrEq(), sliceElem(), boxAssert(), typeSwitch())
	r := returned()
	println(r.X, r.Y, genericEq(), closure(), goroutineArg(), composites(), multiAndVariadic(), boxThenCopy())
}
