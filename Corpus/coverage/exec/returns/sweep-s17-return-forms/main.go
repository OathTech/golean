package main

// Sweep lane sweep/s17-forms (2026-11-05), shape S17 (plan §4; the matrix
// on BUG-012's line): return statements whose operand is a type assertion,
// a receive, a map read, an append, a struct literal, an address of a
// literal, a slice literal, an immediate func literal call, two builtins, a
// nil pair, a conversion; and a return from inside a select case and a type
// switch clause. Expected = gc go1.26.5.

type pt struct{ x, y int }

// A10.2
func retAssert() int {
	var x any = 5
	return x.(int)
}

func retRecv() int {
	ch := make(chan int, 1)
	ch <- 6
	return <-ch
}

func retMapGet() int {
	m := map[string]int{"a": 7}
	return m["a"]
}

func retAppendInner() []int {
	s := []int{1}
	return append(s, 2)
}

func retAppend() int {
	s := retAppendInner()
	return len(s)*10 + s[1] // 22
}

func retStructLit() pt {
	return pt{1, 2}
}

func retAddrLitInner() *pt {
	return &pt{3, 4}
}

func retAddrLit() int {
	p := retAddrLitInner()
	return p.x*10 + p.y // 34
}

func retSliceLitInner() []int {
	return []int{1, 2}
}

func retSliceLit() int {
	s := retSliceLitInner()
	return len(s)*10 + s[0] + s[1] // 23
}

func retFunclitCall() int {
	return func() int { return 7 }()
}

func retLenCap() (int, int) {
	s := make([]int, 2, 5)
	return len(s), cap(s)
}

func retNilNilInner() (*pt, error) {
	return nil, nil
}

func retNilNil() int {
	p, e := retNilNilInner()
	r := 0
	if p == nil {
		r += 1
	}
	if e == nil {
		r += 10
	}
	return r // 11
}

func retConversion() int64 {
	x := 9
	return int64(x)
}

// A10.4
func retFromSelect() int {
	ch := make(chan int, 1)
	ch <- 10
	for {
		select {
		case v := <-ch:
			return v
		}
	}
}

func retFromTypeSwitch() int {
	var v any = 11
	switch t := v.(type) {
	case int:
		return t
	}
	return -1
}

func main() {
	a, b := retLenCap()
	println(retAssert(), retRecv(), retMapGet(), retAppend(), retStructLit().x, retAddrLit(), retSliceLit(),
		retFunclitCall(), a, b, retNilNil(), retConversion(), retFromSelect(), retFromTypeSwitch())
}
