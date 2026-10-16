package main

// RED BY DESIGN since the 2026-10-14 ruling ([USER] Mike, both halves agreed,
// BUG-129): a call or an index expression at a blank field is not a
// constant, nil or a plain variable read, so each literal here refuses by
// name (FAIL/frontend-export, by-design/blank-field-operand). Born
// 2026-10-13 as PASS rows pinning a panicking call operand, a panicky index
// operand and the spec-unsequenced «panicky blank residual beside a sibling
// call» pair on both paths; gc's answers stand in the rows.

type blankPanicS struct {
	_ int
	X int
}

// A float field keeps the literal on the legacy ANF path (outside the
// unseq sweep's type grammar).
type blankPanicF struct {
	_ int
	X float64
}

func blankPanicBoom() int {
	panic("blank operand boom")
}

func blankPanicWit(v int) int {
	println("wit", v)
	return v
}

func blankPanicCallOperand() {
	println("before")
	s := blankPanicS{blankPanicBoom(), 2}
	println("after", s.X)
}

func blankPanicIndexOperand() {
	xs := []int{1, 2, 3}
	i := 5
	println("before")
	s := blankPanicS{xs[i], 2}
	println("after", s.X)
}

// The unseq sweep path (int fields, a top-level call, a checked access).
func blankPanicIndexThenCallSweep() {
	xs := []int{1, 2, 3}
	i := 5
	s := blankPanicS{xs[i], blankPanicWit(1)}
	println("after", s.X)
}

// The legacy path: the residual sits at its field position after the
// hoisted call; its E13 probe offers the other order.
func blankPanicIndexThenCallLegacy() {
	xs := []int{1, 2, 3}
	i := 5
	s := blankPanicF{xs[i], float64(blankPanicWit(1))}
	println("after", s.X > 0)
}

func blankPanicRecoveredValue() (r int) {
	defer func() {
		if recover() != nil {
			r = 1
		}
	}()
	xs := []int{1}
	i := 3
	_ = blankPanicS{xs[i], 2}
	return 0
}
