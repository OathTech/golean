package main

// Sweep lane sweep/s17-forms (2026-11-05), shape S17 (plan §4; the matrix
// on BUG-024's line): expression switches at the shapes the corpus did not
// hold — an empty body with and without a tag or an init (the tag still
// evaluated), a default-only body, inits that are IncDec / send / receive /
// call / compound statements, tags of bool / pointer / chan / defined-int /
// rune kinds and the `false` literal, a tagless multi-value case, case
// expressions that are a receive / a conversion / an index / an assertion,
// a switch inside a select inside a for, in a closure and in a generic body.
// Expected = gc go1.26.5.

var calls int

func bump() int { calls++; return calls }

// A16.2
func emptyTagless() int {
	switch {
	}
	return 1
}

func emptyTagEval() int {
	calls = 0
	switch bump() {
	}
	return calls // 1: the tag is evaluated even with no clause
}

func emptyInitTag() int {
	calls = 0
	switch x := bump(); x {
	}
	return calls // 1
}

func emptyInitNoTag() int {
	calls = 0
	switch bump(); {
	}
	return calls // 1
}

// A16.3
func defaultOnlyTagless() int {
	n := 0
	switch {
	default:
		n = 5
	}
	return n // 5
}

func defaultOnlyTag() int {
	n := 0
	x := 3
	switch x {
	default:
		n = 6
	}
	return n // 6
}

// A16.4
func initIncdec() int {
	i, r := 0, 0
	switch i++; i {
	case 1:
		r = 10
	default:
		r = 20
	}
	return r*10 + i // 101
}

func initSend() int {
	ch := make(chan int, 2)
	r := 0
	switch ch <- 3; len(ch) {
	case 1:
		r = <-ch
	}
	return r // 3
}

func initRecv() int {
	ch := make(chan int, 2)
	ch <- 4
	ch <- 5
	r := 0
	switch <-ch; len(ch) {
	case 1:
		r = <-ch
	}
	return r // 5
}

func initCall() int {
	calls = 0
	r := 0
	switch bump(); calls {
	case 1:
		r = 7
	}
	return r // 7
}

func initCompound() int {
	i, r := 0, 0
	switch i += 5; i {
	case 5:
		r = 8
	}
	return r*10 + i // 85
}

// A16.5
func tagBool(k int) int {
	b := k != 0
	switch b {
	case true:
		return 1
	case false:
		return 2
	}
	return 0
}

func tagPointer() int {
	x, y := 1, 2
	p := &x
	q := &y
	r := 0
	switch p {
	case q:
		r = 1
	case &x:
		r = 2
	}
	return r // 2
}

func tagChan() int {
	c1 := make(chan int)
	c2 := make(chan int)
	r := 0
	switch c1 {
	case c2:
		r = 1
	case c1:
		r = 2
	}
	return r // 2
}

type kind int

const (
	kA kind = iota + 1
	kB
)

func tagDefinedInt() int {
	k := kB
	switch k {
	case kA:
		return 1
	case kB:
		return 2
	}
	return 0
}

func tagRune() int {
	c := 'c'
	switch c {
	case 'a':
		return 1
	case 'b', 'c':
		return 2
	}
	return 0
}

// A16.6
func tagFalseLiteral() int {
	x := 0
	r := 0
	switch false {
	case x > 1:
		r = 1 // false == (0 > 1) matches first
	case x < 1:
		r = 2
	default:
		r = 3
	}
	return r // 1
}

// A16.7
func taglessMultiValue() int {
	a, b := 0, 2
	r := 0
	switch {
	case a > 1, b > 1:
		r = 1
	default:
		r = 2
	}
	return r // 1
}

// A16.8
func caseRecv() int {
	ch := make(chan int, 1)
	ch <- 5
	x := 5
	r := 0
	switch x {
	case <-ch:
		r = 1
	default:
		r = 2
	}
	return r*10 + len(ch) // 10
}

func caseConversion() int {
	f := 2.0
	x := 2
	r := 0
	switch x {
	case int(f):
		r = 1
	}
	return r // 1
}

func caseIndex() int {
	a := []int{1, 2}
	x := 2
	r := 0
	switch x {
	case a[0]:
		r = 1
	case a[1]:
		r = 2
	}
	return r // 2
}

func caseAssert() int {
	var i any = 3
	x := 3
	r := 0
	switch x {
	case i.(int):
		r = 1
	}
	return r // 1
}

// A16.9
func switchInSelectInFor() int {
	ch := make(chan int, 3)
	ch <- 1
	ch <- 2
	ch <- 3
	n := 0
	for i := 0; i < 3; i++ {
		select {
		case v := <-ch:
			switch v {
			case 2:
				break // the switch
			case 3:
				continue // the for
			}
			n += v
		}
		n += 10
	}
	return n // v=1: 1+10; v=2: break leaves the switch only, then 2+10; v=3: continue -> 23
}

// A16.11
func switchInClosure() int {
	f := func(x int) int {
		switch x {
		case 1:
			return 10
		default:
			return 20
		}
	}
	return f(1) + f(2) // 30
}

func swG[T comparable](x, y T) int {
	switch x {
	case y:
		return 1
	}
	return 0
}

func switchInGeneric() int {
	return swG(1, 1)*10 + swG("a", "b") // 10
}

func main() {
	println(emptyTagless(), emptyTagEval(), emptyInitTag(), emptyInitNoTag(), defaultOnlyTagless(), defaultOnlyTag(),
		initIncdec(), initSend(), initRecv(), initCall(), initCompound(), tagBool(1), tagBool(0), tagPointer(),
		tagChan(), tagDefinedInt(), tagRune(), tagFalseLiteral(), taglessMultiValue(), caseRecv(), caseConversion(),
		caseIndex(), caseAssert(), switchInSelectInFor(), switchInClosure(), switchInGeneric())
}
