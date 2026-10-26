package main

// S4 sweep (the defect-neighbourhood campaign, lane sweep/s4-identity,
// 2026-10-26): BUG-133's shape — ONE cell under two spellings after a
// struct-tag-compatible pointer conversion — at the ROUTES the 44
// pointers/identity-* rows do not hold: an expression switch, parameter
// binding, channel traffic, a pointer returned by a method on the converted
// receiver, closure capture, a slice/array element's field, a defined type
// over a defined struct, a chained conversion, an embedded POINTER field,
// identity after the whole-struct STORE through the alias (BUG-134's route),
// and arrays/structs HOLDING such pointers (valueEqList / valueEqFields reach
// the pointer arm). Every row agrees with gc at birth (probed both sides
// first; .tmp/probes/fk-* of the lane).

type tagA struct {
	X int `json:"a"`
	Y int `json:"a"`
}
type tagB struct {
	X int `json:"b"`
	Y int `json:"b"`
}
type tagC struct {
	X int `json:"c"`
	Y int `json:"c"`
}
type overB tagB
type overA tagA

func bit(b bool, w int) int {
	if b {
		return w
	}
	return 0
}

// An expression switch on a pointer value: the alias spelling matches the
// original, never a distinct variable's field (gc 21).
func aliasSwitch() int {
	a := tagA{X: 7}
	b := (*tagB)(&a)
	c := tagA{X: 7}
	s := 0
	switch &b.X {
	case &c.X:
		s += 1
	case &a.X:
		s += 20
	default:
		s += 300
	}
	switch p := &a.X; p {
	case &b.X:
		s += 1
	default:
		s += 3000
	}
	return s
}

func same(p, q *int) bool  { return p == q }
func sameBox(p, q any) bool { return p == q }

// Parameter binding: the two spellings bound to *int parameters compare
// equal; the whole-struct pointers boxed at different types do not (gc 111).
func aliasParam() int {
	a := tagA{X: 7}
	b := (*tagB)(&a)
	return bit(same(&a.X, &b.X), 1) + bit(same(&b.X, &a.X), 10) +
		bit(sameBox(&a.X, &b.X), 100) + bit(sameBox(&a, b), 1000)
}

// Channel traffic: pointers sent under both spellings and received compare
// equal; through a chan any likewise (gc 11111).
func aliasChanTraffic() int {
	a := tagA{X: 7}
	b := (*tagB)(&a)
	ch := make(chan *int, 2)
	ch <- &a.X
	ch <- &b.X
	p := <-ch
	q := <-ch
	cb := make(chan any, 1)
	cb <- &b.X
	r := <-cb
	return bit(p == q, 1) + bit(p == &b.X, 10) + bit(q == &a.X, 100) +
		bit(r == any(&a.X), 1000) + bit(r.(*int) == &a.X, 10000)
}

func (b *tagB) px() *int   { return &b.X }
func (a tagA) pxCopy() *int { return &a.X }

// A pointer returned by a pointer-receiver method on the converted receiver
// is the original field; a value receiver's copy is a distinct cell (gc 111).
func aliasMethodReturned() int {
	a := tagA{X: 7}
	b := (*tagB)(&a)
	return bit(b.px() == &a.X, 1) + bit((*tagB)(&a).px() == &a.X, 10) +
		bit(b.px() == b.px(), 100) + bit(a.pxCopy() == &a.X, 1000) +
		bit(a.pxCopy() == a.pxCopy(), 10000)
}

// Closure capture: closures over each spelling return one location (gc 111).
func aliasClosure() int {
	a := tagA{X: 7}
	b := (*tagB)(&a)
	f := func() *int { return &b.X }
	g := func() *int { return &a.X }
	return bit(f() == g(), 1) + bit(f() == &a.X, 10) + bit(g() == &b.X, 100)
}

// The alias of a SLICE element's and an ARRAY element's field; the map over
// both spellings has one entry (gc 1*: 10011 + 100 + 2000 → 12111).
func aliasSliceElem() int {
	as := []tagA{{X: 1}, {X: 2}}
	pb := (*tagB)(&as[0])
	pb1 := (*tagB)(&as[1])
	arr := [2]tagA{{X: 1}, {X: 2}}
	qb := (*tagB)(&arr[1])
	m := map[*int]int{&as[0].X: 1}
	m[&pb.X] = 2
	return bit(&as[0].X == &pb.X, 1) + bit(&as[1].X == &pb1.X, 10) +
		bit(&as[0].X == &pb1.X, 100) + bit(&pb.X == &pb1.X, 1000) +
		bit(&arr[1].X == &qb.X, 10000) + bit(&arr[0].X == &qb.X, 100000) +
		len(m)*1000000 + m[&as[0].X]*10000000
}

// A defined type over a defined struct (`type overB tagB`, `type overA tagA`):
// the field pointers are one location, the boxed struct pointers differ by
// dynamic type; one map entry under three spellings (gc 1+10+100 + 1000000 + 30000000).
func aliasDefinedOverDefined() int {
	a := tagA{X: 7}
	c := (*overB)(&a)
	d := (*overA)(&a)
	m := map[*int]int{&a.X: 1}
	m[&c.X] = 2
	m[&d.X] = 3
	return bit(&a.X == &c.X, 1) + bit(&c.X == &d.X, 10) + bit(any(&a.X) == any(&c.X), 100) +
		bit(any(&a) == any(c), 1000) + bit(any(c) == any(d), 10000) +
		len(m)*1000000 + m[&a.X]*10000000
}

// A chained conversion `(*tagC)((*tagB)(&a))` and the conversion back (gc 1111).
func aliasChained() int {
	a := tagA{X: 7}
	c := (*tagC)((*tagB)(&a))
	back := (*tagA)(c)
	return bit(&a.X == &c.X, 1) + bit(back == &a, 10) + bit(&back.X == &c.X, 100) +
		bit(any(&a.X) == any(&c.X), 1000)
}

type outerPtr struct {
	*tagA
	N int
}

// An embedded POINTER field: the promoted `o.X`, the explicit `o.tagA.X` and
// the converted `(*tagB)(o.tagA).X` are one location; a write through the
// promoted spelling is seen through the alias (gc 1111 + 99*10000).
func aliasEmbeddedPointer() int {
	a := tagA{X: 7}
	o := outerPtr{&a, 1}
	b := (*tagB)(o.tagA)
	s := bit(&o.X == &a.X, 1) + bit(&o.X == &b.X, 10) + bit(&o.tagA.X == &b.X, 100) +
		bit(o.tagA == &a, 1000)
	o.X = 9
	return s + (b.X*10+a.X)*10000
}

// Identity after the WHOLE-STRUCT store through the alias (BUG-134's route):
// pointers taken before the store still name the same cells, the store is
// seen through them, and a later whole-struct assignment to the original
// likewise (gc: 1+10 + 89*100 + 1*10000 + 2*100000 + 34*1000000 + 100000000).
func aliasAfterWholeStore() int {
	a := tagA{X: 1, Y: 2}
	b := (*tagB)(&a)
	p := &a.X
	q := &b.Y
	*b = tagB{X: 8, Y: 9}
	s := bit(p == &b.X, 1) + bit(q == &a.Y, 10) + (*p*10+*q)*100
	m := map[*int]int{p: 1}
	m[&b.X] = 2
	s += len(m)*10000 + m[p]*100000
	a = tagA{X: 3, Y: 4}
	return s + (*p*10+*q)*1000000 + bit(p == &b.X, 100000000)
}

type holder struct {
	P *int
	N int
}

// Arrays holding the two spellings compare equal elementwise (valueEqList
// reaches the pointer arm); a swapped pair is still equal (gc 101).
func aliasHolderArrayEq() int {
	a := tagA{X: 7}
	b := (*tagB)(&a)
	arrA := [1]*int{&a.X}
	arrB := [1]*int{&b.X}
	return bit(arrA == arrB, 1) + bit(arrA != arrB, 10) +
		bit([2]*int{&a.X, &b.X} == [2]*int{&b.X, &a.X}, 100)
}

// Structs holding the two spellings compare equal fieldwise (gc 1).
func aliasHolderStructEq() int {
	a := tagA{X: 7}
	b := (*tagB)(&a)
	hA := holder{&a.X, 1}
	hB := holder{&b.X, 1}
	return bit(hA == hB, 1) + bit(hA == holder{&b.X, 2}, 10)
}

// An ARRAY key holding either spelling is one map entry (gc 21).
func aliasHolderArrayKey() int {
	a := tagA{X: 7}
	b := (*tagB)(&a)
	arrA := [1]*int{&a.X}
	m := map[[1]*int]int{arrA: 1}
	m[[1]*int{&b.X}] = 2
	return len(m)*10 + m[arrA]
}

// A STRUCT key holding either spelling is one map entry (gc 21).
func aliasHolderStructKey() int {
	a := tagA{X: 7}
	b := (*tagB)(&a)
	hA := holder{&a.X, 1}
	m := map[holder]int{hA: 1}
	m[holder{&b.X, 1}] = 2
	return len(m)*10 + m[hA]
}

// Boxed arrays and structs holding the two spellings: same dynamic type, so
// the payloads compare and are equal (gc 11).
func aliasHolderBoxes() int {
	a := tagA{X: 7}
	b := (*tagB)(&a)
	var i1, i2 any = [1]*int{&a.X}, [1]*int{&b.X}
	return bit(i1 == i2, 1) + bit(any(holder{&a.X, 1}) == any(holder{&b.X, 1}), 10)
}

func main() {
	println(aliasSwitch(), aliasParam(), aliasChanTraffic(), aliasMethodReturned(), aliasClosure(),
		aliasSliceElem(), aliasDefinedOverDefined(), aliasChained(), aliasEmbeddedPointer(),
		aliasAfterWholeStore(), aliasHolderArrayEq(), aliasHolderStructEq(), aliasHolderArrayKey(),
		aliasHolderStructKey(), aliasHolderBoxes())
}
