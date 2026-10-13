package main

// Blank struct fields take the zero value (spec#Comparison_operators:
// «corresponding non-blank field values»; gc compare/compare.go skips
// them). BUG-129; the operand's evaluation beyond calls and the operands
// gc keeps is BUG-129's OPEN F1/F2.

type blankEqS struct {
	_ int
	X int
}

type blankEqDup struct {
	_ int
	_ int
	X int
}

type blankEqT struct {
	_ any
	X int
}

type blankEqInner struct {
	_ int
	Y int
}

type blankEqOuter struct {
	_  blankEqInner
	In blankEqInner
	Z  int
}

type blankEqG[T any] struct {
	_ T
	X int
}

type blankEqS2 blankEqS

func blankEqBit(b bool) int {
	if b {
		return 1
	}
	return 0
}

func blankEqDifferingBlanks() int {
	a, b := blankEqS{1, 2}, blankEqS{9, 2}
	println(a == b, a != b, a == blankEqS{3, 2}, a == blankEqS{1, 3})
	return blankEqBit(a == b)*1000 + blankEqBit(a != b)*100 + blankEqBit(a == blankEqS{3, 2})*10 + blankEqBit(a == blankEqS{1, 3})
}

func blankEqDuplicateBlanks() int {
	a, b := blankEqDup{1, 2, 3}, blankEqDup{4, 5, 3}
	println(a == b, a == blankEqDup{1, 2, 4})
	return blankEqBit(a == b)*10 + blankEqBit(a == blankEqDup{1, 2, 4})
}

func blankEqInterfaceSliceSelf() int {
	a := blankEqT{[]int{1}, 2}
	b := blankEqT{map[string]int{"k": 1}, 2}
	println(a == a, a == b, a == blankEqT{nil, 2}, a == blankEqT{nil, 3})
	return blankEqBit(a == a)*1000 + blankEqBit(a == b)*100 + blankEqBit(a == blankEqT{nil, 2})*10 + blankEqBit(a == blankEqT{nil, 3})
}

func blankEqInterfaceRecovered() (r int) {
	defer func() {
		if recover() != nil {
			r = 99
		}
	}()
	a := blankEqT{[]int{1}, 2}
	if a == a {
		return 7
	}
	return 3
}

func blankEqNestedLiteral() int {
	a := blankEqOuter{blankEqInner{1, 2}, blankEqInner{3, 4}, 5}
	b := blankEqOuter{blankEqInner{6, 7}, blankEqInner{8, 4}, 5}
	println(a == b, a.In == b.In, a.In.Y)
	return blankEqBit(a == b)*100 + blankEqBit(a.In == b.In)*10 + a.In.Y
}

func blankEqPointerLiteral() int {
	p, q := &blankEqS{1, 2}, &blankEqS{9, 2}
	println(*p == *q, p == q, p.X+q.X)
	return blankEqBit(*p == *q)*100 + blankEqBit(p == q)*10 + p.X + q.X
}

func blankEqGenericInstantiation() int {
	a, b := blankEqG[int]{1, 2}, blankEqG[int]{9, 2}
	c, d := blankEqG[string]{"x", 2}, blankEqG[string]{"y", 2}
	println(a == b, c == d)
	return blankEqBit(a == b)*10 + blankEqBit(c == d)
}

func blankEqElementLiterals() int {
	xs := []blankEqS{{1, 2}, {9, 2}}
	arr := [2]blankEqS{{3, 4}, {5, 4}}
	m := map[string]blankEqS{"a": {6, 7}, "b": {8, 7}}
	println(xs[0] == xs[1], arr[0] == arr[1], m["a"] == m["b"], xs[0] == m["a"])
	return blankEqBit(xs[0] == xs[1])*1000 + blankEqBit(arr[0] == arr[1])*100 + blankEqBit(m["a"] == m["b"])*10 + blankEqBit(xs[0] == m["a"])
}

func blankEqConversionCopy() int {
	a := blankEqS{1, 2}
	c := blankEqS2(a)
	d := blankEqS2{9, 2}
	e := a
	e.X = 2
	println(c == d, blankEqS(d) == a, e == a)
	return blankEqBit(c == d)*100 + blankEqBit(blankEqS(d) == a)*10 + blankEqBit(e == a)
}
