package main

// Sweep lane sweep/s17-forms (2026-11-05), shape S17 (plan §4; the matrix
// on BUG-147's line): type assertions used as operands of a further
// selector, call, index, slice or map read; assertions in a condition, a
// return, an argument, a defer argument, a closure and a generic body; and
// calls through a struct-field func value and a call's result in VALUE
// position, plus a call of a converted func value. Expected = gc go1.26.5.

var calls int

type pt struct{ x, y int }

func (p pt) sum() int { return p.x + p.y }

type summer interface{ sum() int }

type holder struct{ f func(int) int }

type adder func(int) int

func take(x int) { calls += x }

func mkAdd() func(int) int { return func(x int) int { return x + 100 } }

func boxG[T any](v T) any { return v }

// B7.2
func assertField() int {
	var i any = pt{1, 2}
	return i.(pt).x*10 + i.(pt).y // 12
}

func assertMethod() int {
	var i any = pt{3, 4}
	return i.(pt).sum() // 7
}

func assertIfaceMethod() int {
	var i any = pt{5, 6}
	return i.(summer).sum() // 11
}

func assertIndex() int {
	var i any = []int{7, 8}
	return i.([]int)[1] // 8
}

func assertPtrField() int {
	var i any = &pt{9, 1}
	return i.(*pt).x*10 + i.(*pt).y // 91
}

func assertSlice() int {
	var i any = "hello"
	s := i.(string)[1:3]
	return len(s)*100 + int(s[0]) // 301
}

func assertMapRead() int {
	var i any = map[string]int{"a": 2}
	return i.(map[string]int)["a"] // 2
}

// B7.3
func assertCond() int {
	var i any = 3
	r := 0
	if i.(int) > 2 {
		r = 1
	}
	return r // 1
}

func assertReturn() int {
	var i any = 4
	return i.(int)
}

func assertArg() int {
	calls = 0
	var i any = 5
	take(i.(int))
	return calls // 5
}

func assertDeferArg() int {
	calls = 0
	var i any = 6
	func() {
		defer take(i.(int))
		i = 100
	}()
	return calls // 6
}

func assertInClosure() int {
	var i any = 7
	f := func() int { return i.(int) * 2 }
	return f() // 14
}

func assertInGeneric() int {
	return boxG(8).(int)*10 + len(boxG("ab").(string)) // 82
}

// B8.2 (value position)
func callFieldFuncValue() int {
	h := holder{f: func(x int) int { return x * 2 }}
	return h.f(4) + 1 // 9
}

func callCallValue() int {
	return mkAdd()(5) // 105
}

// B8.7
func callConvertedFunc() int {
	f := func(x int) int { return x + 1 }
	return adder(f)(1)*10 + (func(int) int)(f)(2) // 20 + 3 = 23
}

func main() {
	println(assertField(), assertMethod(), assertIfaceMethod(), assertIndex(), assertPtrField(), assertSlice(),
		assertMapRead(), assertCond(), assertReturn(), assertArg(), assertDeferArg(), assertInClosure(),
		assertInGeneric(), callFieldFuncValue(), callCallValue(), callConvertedFunc())
}
