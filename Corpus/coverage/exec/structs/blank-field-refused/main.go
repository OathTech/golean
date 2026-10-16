package main

// RED BY DESIGN ([USER] Mike 2026-10-14, both halves agreed; BUG-129): the
// classes gc DROPS at a blank field, refused by name. gc elides a
// side-effect-free blank operand TOGETHER WITH its run-time panic
// (walk/complit.go:231 via staticinit.isSideEffect — shifts, interface
// comparisons, under any pure wrapper), so an evaluating model answers a
// panic where gc answers a value; at a blank field the frontend admits
// only a constant, nil or a plain variable read and refuses the literal
// otherwise (FAIL/frontend-export, by-design/blank-field-operand). gc's
// answers stand in the rows.

type blankRefS struct {
	_ int
	X int
	_ int
}

type blankRefB struct {
	_ bool
	X int
}

type blankRefT struct {
	_ any
	X int
}

type blankRefInner struct {
	_ int
	Y int
}

type blankRefNI struct {
	A blankRefInner
	B blankRefInner
	X int
}

func blankRefMk() (any, any) { return []int{1}, []int{1} }

// gc 2: the negative-shift panic is elided with the operand.
func blankRefNegativeShift() int {
	n := -1
	s := blankRefS{1 << n, 2, 3}
	return s.X
}

// gc 2: the «comparing uncomparable type» panic is elided with the operand.
func blankRefInterfaceCompare() int {
	a, b := blankRefMk()
	s := blankRefB{a == b, 2}
	return s.X
}

// gc 9: a unary wrapper over the shift, inside a nested literal at a
// NON-blank outer field — the inner literal's blank field refuses.
func blankRefNestedPureWrapper() int {
	n := -1
	s := blankRefNI{blankRefInner{7, 2}, blankRefInner{-(1 << n), 4}, 5}
	return s.X + s.B.Y
}

// gc 7: the Codex zero-context pass's own F1 program — a composite literal
// at an interface-typed blank field is not an admitted operand, so the
// program refuses by name rather than answering (it answered 99 at the
// branch base, 7 on the 2026-10-13 lowering).
func blankRefCompositeOperand() (r int) {
	defer func() {
		if recover() != nil {
			r = 99
		}
	}()
	a := blankRefT{[]int{1}, 2}
	if a == a {
		return 7
	}
	return 3
}
