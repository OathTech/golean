package main

// Sweep S8 (lane sweep/s8-unseq, 2026-10-27) — BUG-310: the operand kinds gc evaluates
// EARLY (before a lexically later sibling call) — a type assertion to a non-pointer-shaped
// type, a slice expression, a string slice — at the sweeps the `unseq` grammar DECLINES
// (a statement form: if / for / switch conditions, var specs, the send statement; defer
// and go argument lists; a lifted body: a stored, invoked or deferred func literal; a
// generic body with a T result; a parameter or operand type outside the grammar: an
// interface, a defined integer, a func type, an array; an interface method call as the
// event). The legacy ANF path hoists the call ahead and reads the operand in the residual
// AFTER it — the call-first member alone — where gc realizes the operand-first member
// (order.go's safe-expression copy of ODOTTYPE / OSLICE* at their lexical position). The
// in-grammar twins are membership rows elsewhere in sweep-s8-*; the four `ctl-*` rows
// here are the assertion targets the grammar ADMITS (struct, pointer, string, slice).

type MyInt int

type T2 struct{ n int }

func (t T2) M() int { return t.n }

type I2 interface{ M() int }

type I3 interface{ M() int }

type O struct{ piv *any }

func (o *O) SetIv() int { *o.piv = 5; return 10 }

type IvSetter interface{ SetIv() int }

func sink(a, b int) int { return a*100 + b }

func sinkD(r *int, a, b int) { *r = a*100 + b }

func sink2(ch chan int, a, b int) { ch <- a*100 + b }

func sinkI(i I2, k int) int { return i.M() + k }

func sinkI3(i I3, k int) int { return i.M()*100 + k }

func sinkMI(m MyInt, k int) int { return int(m)*100 + k }

func sinkMI2(r *int, a MyInt, b int) { *r = int(a)*100 + b }

func sinkFn(fn func() int, a, b int) int { return fn() + a*100 + b }

func sinkT(t T2, k int) int { return t.n*100 + k }

func sinkP(p *T2, k int) int { return p.n*100 + k }

func sinkS(s string, k int) int { return int(s[0])*100 + k }

func sinkSl(s []int, k int) int { return s[0]*100 + k }

// --- the type assertion (gc early; the legacy residual late) ---

func ifCondAssertion() int {
	var iv any = 1
	f := func() int { iv = 5; return 3 }
	if iv.(int) > f() {
		return 1
	}
	return 0
}

func forCondAssertion() int {
	var iv any = 1
	f := func() int { iv = 5; return 3 }
	n := 0
	for iv.(int) < f() {
		n++
		iv = 10
	}
	return n
}

func switchCaseAssertion() int {
	var iv any = 1
	f := func() int { iv = 5; return 3 }
	switch {
	case iv.(int) > f():
		return 1
	}
	return 0
}

func varSpecAssertion() int {
	var iv any = 1
	set := func() int { iv = 5; return 10 }
	var v = iv.(int) + set()
	return v
}

func sendValueAssertion() int {
	ch1 := make(chan int, 1)
	fch := func() chan int { return ch1 }
	var iv any = 1
	f := func() int { iv = 5; return 0 }
	fch() <- iv.(int) + f()
	return <-ch1
}

func deferArgAssertion() int {
	r := 0
	var iv any = 1
	set := func() int { iv = 5; return 10 }
	func() {
		defer sinkD(&r, iv.(int), set())
	}()
	return r
}

func goArgAssertion() int {
	ch := make(chan int, 1)
	var iv any = 1
	set := func() int { iv = 5; return 10 }
	go sink2(ch, iv.(int), set())
	return <-ch
}

func closureBodyAssertion() int {
	var iv any = 1
	set := func() int { iv = 5; return 10 }
	fn := func() int { return iv.(int) + set() }
	return fn()
}

func invokedLitAssertion() int {
	var iv any = 1
	set := func() int { iv = 5; return 10 }
	return func() int { return iv.(int) + set() }()
}

func deferredLitAssertion() int {
	r := 0
	var iv any = 1
	set := func() int { iv = 5; return 10 }
	func() {
		defer func() { r = iv.(int) + set() }()
	}()
	return r
}

func eventIfaceMethodCallAssertion() int {
	var iv any = 1
	var i IvSetter = &O{piv: &iv}
	return iv.(int) + i.SetIv()
}

func ifaceParamAssertion() int {
	var iv any = T2{1}
	set := func() int { iv = T2{5}; return 10 }
	return sinkI(iv.(I2), set())
}

func ifaceToIfaceParamAssertion() int {
	var i I2 = T2{1}
	set := func() int { i = T2{5}; return 10 }
	return sinkI3(i.(I3), set())
}

func definedIntParamAssertion() int {
	var iv any = MyInt(1)
	set := func() int { iv = MyInt(5); return 10 }
	return sinkMI(iv.(MyInt), set())
}

func funcParamAssertion() int {
	var iv any = 1
	f := func() int { iv = 5; return 10 }
	return sinkFn(func() int { return 0 }, iv.(int), f())
}

func arrayOperandAssertion() int {
	arr := [2]int{0, 0}
	var iv any = 1
	f := func() int { iv = 5; return 10 }
	return arr[0] + iv.(int) + f()
}

func assertionLeftArrayOperand() int {
	arr := [2]int{0, 0}
	var iv any = 1
	f := func() int { iv = 5; return 10 }
	return iv.(int) + arr[0] + f()
}

func arrayTargetAssertion() int {
	var arr [6]int
	var iv any = 1
	f := func() int { iv = 5; return 7 }
	arr[iv.(int)] = f()
	return arr[1]*10 + arr[5]
}

// --- the slice expression (gc early; the legacy residual panics after the call moved the bound) ---

func ifCondSliceExpr() int {
	s := []int{1, 5}
	j := 1
	f := func() int { j = 9; return 3 }
	if s[j:][0] > f() {
		return 1
	}
	return 0
}

func forCondSliceExpr() int {
	s := []int{1, 5}
	j := 0
	f := func() int { j = 9; return 3 }
	n := 0
	for s[j:][0] < f() {
		n++
		j = 1
		if n > 3 {
			break
		}
	}
	return n
}

func varSpecSliceExpr() int {
	s := []int{1, 5}
	j := 1
	f := func() int { j = 9; return 10 }
	var v = s[j:][0] + f()
	return v
}

func deferArgSliceExpr() int {
	r := 0
	s := []int{1, 5}
	j := 1
	f := func() int { j = 9; return 10 }
	func() {
		defer sinkD(&r, s[j:][0], f())
	}()
	return r
}

func goArgSliceExpr() int {
	ch := make(chan int, 1)
	s := []int{1, 5}
	j := 1
	f := func() int { j = 9; return 10 }
	go sink2(ch, s[j:][0], f())
	return <-ch
}

func definedIntParamSliceExpr() int {
	r := 0
	s := []MyInt{1, 5}
	j := 1
	f := func() int { j = 9; return 10 }
	sinkMI2(&r, s[j:][0], f())
	return r
}

func genSliceExpr[T int | int64](s []T, pj *int, set func() T) T { return s[*pj:][0] + set() }

func genericBodySliceExpr() int {
	s := []int{1, 5}
	j := 1
	set := func() int { j = 9; return 10 }
	return genSliceExpr(s, &j, set)
}

// --- the string slice (gc early) ---

func ifCondStringSlice() int {
	str := "ab"
	f := func() int { str = "zz"; return 100 }
	if int(str[1:][0]) > f() {
		return 1
	}
	return 0
}

func varSpecStringSlice() int {
	str := "ab"
	f := func() int { str = "zz"; return 1 }
	var v = int(str[1:][0]) + f()
	return v
}

func deferArgStringSlice() int {
	r := 0
	str := "ab"
	f := func() int { str = "zz"; return 1 }
	func() {
		defer sinkD(&r, int(str[1:][0]), f())
	}()
	return r
}

func closureBodyStringSlice() int {
	str := "ab"
	f := func() int { str = "zz"; return 1 }
	fn := func() int { return int(str[1:][0]) + f() }
	return fn()
}

// --- controls: assertion targets the grammar ADMITS (membership, gc's early member inside) ---

func ctlStructParamAssertion() int {
	var iv any = T2{1}
	set := func() int { iv = T2{5}; return 10 }
	return sinkT(iv.(T2), set())
}

func ctlPointerParamAssertion() int {
	var iv any = &T2{1}
	set := func() int { iv = &T2{5}; return 10 }
	return sinkP(iv.(*T2), set())
}

func ctlStringParamAssertion() int {
	var iv any = "a"
	set := func() int { iv = "z"; return 10 }
	return sinkS(iv.(string), set())
}

func ctlSliceParamAssertion() int {
	var iv any = []int{1}
	set := func() int { iv = []int{5}; return 10 }
	return sinkSl(iv.([]int), set())
}
