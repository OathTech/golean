package main

// Sweep lane sweep/s13-binding (2026-10-27), shape S13 (plan §4; the matrix on
// BUG-068/069/148/003/142's Neighbourhood lines). Named results shadowed at every
// declaration form the rename set (tools/nativefrontend/resultshadow.go) admits
// and at the forms beside it: a closure over the result called under a live
// shadow, the self-referential shadows, the multi-value call, select cases, the
// one-target receive, if/switch/for inits, the ASSIGN-form range and for-clause
// writing the real result, func literals with a parameter or a result of the
// same name, const/type/label shadows, the mixed redeclaration at the top level.
// Every subject returns its named result(s): the return/frame-exit seam is the
// observation. Expected = gc go1.26.5.

// A2: a closure declared before the shadow block writes the RESULT while the shadow is live.
func closureWritesResultUnderShadow() (r int) {
	set := func(v int) { r = v }
	r = 1
	{
		r := 10
		set(r + 5) // the result slot: 15; the shadow stays 10
		_ = r
	}
	return // 15
}

// A5: the self-referential var shadow reads the RESULT (BUG-142 x BUG-068).
func varSelfShadow() (r int) {
	r = 4
	{
		var r = r + 1 // the initializer's r is the result: 5
		if r != 5 {
			return -1
		}
	}
	return // 4
}

// A6 (and A31): `r := r * 2` in a nested block; a plain map read on the shadow.
func defineSelfShadow() (r int) {
	r = 3
	m := map[int]int{1: 100}
	{
		r := r * 2 // 6
		r += m[1]  // 106
		if r != 106 {
			return -1
		}
	}
	return // 3
}

func pair() (int, int) { return 7, 8 }

// A7: a multi-value call define shadowing the result.
func multiCallShadow() (r int) {
	r = 1
	{
		r, x := pair() // the shadow r = 7
		if r+x != 15 {
			return -1
		}
	}
	return // 1
}

// A8: a select case shadowing the result.
func selectCaseShadow() (r int) {
	r = 1
	ch := make(chan int, 1)
	ch <- 40
	select {
	case r := <-ch:
		if r != 40 {
			return -1
		}
	}
	return // 1
}

// A9: the two-target select case.
func selectCaseTwoShadow() (r int, ok bool) {
	r, ok = 1, false
	ch := make(chan int, 1)
	ch <- 50
	select {
	case r, ok := <-ch:
		if !ok || r != 50 {
			return -1, false
		}
	}
	return // 1, false
}

// A10: an if-init shadow; the else branch sees the shadow, the code after sees the result.
func ifInitShadow() (r int) {
	r = 2
	if r := 15; r > 100 {
		return -1
	} else {
		if r != 15 {
			return -2
		}
	}
	return // 2
}

// A11: a switch-init shadow.
func switchInitShadow() (r int) {
	r = 2
	switch r := 9; r {
	case 9:
		if r != 9 {
			return -1
		}
	default:
		return -2
	}
	return // 2
}

// A12: a plain (uncaptured) for-clause shadow.
func forInitShadowPlain() (r int) {
	r = 100
	sum := 0
	for r := 0; r < 3; r++ {
		sum += r
	}
	return r + sum // 103
}

// A13: a for-clause shadow whose address escapes (the per-iteration path under the rename).
func forInitShadowAddr() (r int) {
	r = 100
	var ps []*int
	for r := 0; r < 3; r++ {
		ps = append(ps, &r)
	}
	return r + *ps[0]*100 + *ps[1]*10 + *ps[2] // 112
}

// A14b: the ASSIGN-form range writes the real result.
func rangeAssignWritesResult() (r int) {
	r = -1
	for r = range []int{10, 20, 30} {
	}
	return // 2
}

// A16: a func literal parameter named like the enclosing result.
func litParamSameName() (r int) {
	r = 1
	f := func(r int) int { return r * 2 }
	r += f(10) // 21
	return
}

// A17: a func literal with its own named result of the same name.
func litOwnResultSameName() (r int) {
	r = 1
	f := func() (r int) { r = 5; return }
	r += f() // 6
	return
}

// A18: the literal's own result shadowed inside the literal (the literal's own rename set).
func litOwnResultShadowed() (r int) {
	r = 1
	f := func() (r int) {
		r = 5
		{
			r := 50
			_ = r
		}
		return
	}
	r += f() // 6
	return
}

// A19: the shadow captured by a closure called after its block exits.
func shadowCapturedOutlivesBlock() (r int) {
	r = 1
	var g func() int
	{
		r := 10
		g = func() int { r++; return r }
	}
	r += g() + g() // 1 + 11 + 12 = 24
	return
}

// A20: a defer inside the shadow block captures the SHADOW, not the result.
func deferCapturesShadow() (r int) {
	r = 1
	{
		r := 10
		defer func() { r += 100 }() // the shadow's cell: unobservable at exit
		_ = r
	}
	return // 1
}

// A21: a local const shadowing the result.
func constShadow() (r int) {
	r = 1
	{
		const r = 7
		if r != 7 {
			return -1
		}
	}
	return // 1
}

// A22: a local type shadowing the result.
func typeShadow() (r int) {
	r = 1
	{
		type r int
		x := r(3)
		if int(x) != 3 {
			return -1
		}
	}
	return // 1
}

// A23: two results shadowed by one define.
func twoResultsOneDefine() (n int, s string) {
	n, s = 1, "a"
	{
		n, s := 2, "b"
		_ = n
		_ = s
	}
	return // 1, "a"
}

// A30: the one-target receive define shadowing the result (emitChanRecvAssign's define path).
func recvOneTargetShadow() (r int) {
	r = 1
	ch := make(chan int, 1)
	ch <- 60
	{
		r := <-ch
		if r != 60 {
			return -1
		}
	}
	return // 1
}

// A32: a single-value type assertion define shadowing the result.
func assertOneValueShadow() (r int) {
	r = 1
	var x any = 70
	{
		r := x.(int)
		if r != 70 {
			return -1
		}
	}
	return // 1
}

// A34: a label named like the result (labels have their own namespace).
func labelSameName() (r int) {
	r = 0
r:
	r++
	if r < 3 {
		goto r
	}
	return // 3
}

// A35: the result as the ASSIGN-form for-clause variable.
func forAssignResult() (r int) {
	for r = 0; r < 3; r++ {
	}
	return // 3
}

// E9: the mixed redeclaration at the top level reassigns the result.
func mixedRedeclResult() (r int) {
	r, x := 1, 2
	r += x
	return // 3
}

func main() {
	println(closureWritesResultUnderShadow(), varSelfShadow(), defineSelfShadow(), multiCallShadow(),
		selectCaseShadow(), ifInitShadow(), switchInitShadow(), forInitShadowPlain(), forInitShadowAddr(),
		rangeAssignWritesResult(), litParamSameName(), litOwnResultSameName(), litOwnResultShadowed(),
		shadowCapturedOutlivesBlock(), deferCapturesShadow(), constShadow(), typeShadow(),
		recvOneTargetShadow(), assertOneValueShadow(), labelSameName(), forAssignResult(), mixedRedeclResult())
	println(selectCaseTwoShadow())
	println(twoResultsOneDefine())
}
