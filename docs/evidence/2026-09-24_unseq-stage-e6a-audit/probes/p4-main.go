package main

// Audit probes — Stage E6a attack 5: every declaration form a graph atom may name (R1 coverage), and the
// F8 / mS4 shapes for the decoder mutants.

func wit(x int) int { println("wit", x); return x }

type T struct{ n int }

func pNamedResult(s []int, i int) (r int) {
	r = s[i] + wit(1)
	return
}

func pRangeSlice() int {
	xs := []int{0, 5}
	r := 0
	for i, v := range xs {
		r += xs[v] + wit(i)
	}
	return r
}

func pRangeMap() int {
	m := map[int]int{1: 0}
	s := []int{7}
	r := 0
	for k, v := range m {
		r += s[v] + wit(k)
	}
	return r
}

func pRangeChan() int {
	ch := make(chan int, 2)
	ch <- 0
	ch <- 9
	close(ch)
	s := []int{7}
	r := 0
	for v := range ch {
		r += s[v] + wit(1)
	}
	return r
}

func pRangeInt() int {
	s := []int{7}
	r := 0
	for i := range 3 {
		r += s[i] + wit(1)
	}
	return r
}

func pRangeString() int {
	s := []int{7}
	r := 0
	for i, c := range "a" {
		r += s[int(c)-97] + wit(i)
	}
	return r
}

func pShadow() int {
	x := 1
	s := []int{7}
	r := s[x-1] + wit(1)
	{
		x := "ab"
		r += int(x[9]) + wit(2)
	}
	return r
}

func pSelect() int {
	ch := make(chan int, 1)
	ch <- 0
	s := []int{7}
	r := 0
	select {
	case v := <-ch:
		r = s[v] + wit(1)
	}
	return r
}

func pSelectOk() int {
	ch := make(chan int, 1)
	ch <- 0
	s := []int{7}
	r := 0
	select {
	case v, ok := <-ch:
		if ok {
			r = s[v] + wit(1)
		}
	}
	return r
}

func pTypeSwitch() int {
	var iv interface{} = 0
	s := []int{7}
	r := 0
	switch v := iv.(type) {
	case int:
		r = s[v] + wit(1)
	case string:
		r = len(v) + wit(2)
	}
	return r
}

func pIfInit() int {
	s := []int{7}
	if v := wit(0); v >= 0 {
		return s[v] + wit(1)
	}
	return 0
}

func pCommaOk() int {
	m := map[int]int{1: 0}
	s := []int{7}
	if v, ok := m[1]; ok {
		return s[v] + wit(1)
	}
	return 0
}

func pVarDecl() int {
	var v int = 0
	var a, b int = 0, 0
	s := []int{7}
	return s[v+a+b] + wit(1)
}

func pTypeAssertDecl() int {
	var iv interface{} = 0
	v := iv.(int)
	s := []int{7}
	return s[v] + wit(1)
}

func pRecvDecl() int {
	ch := make(chan int, 2)
	ch <- 0
	ch <- 0
	v := <-ch
	v2, ok := <-ch
	s := []int{7}
	if ok {
		return s[v+v2] + wit(1)
	}
	return 0
}

func pClosureCapture() int {
	x := 0
	s := []int{7}
	f := func() int { x = 9; return 1 }
	return s[x] + f()
}

func pLiftedBody() int {
	s := []int{7}
	x := 0
	g := func() int { return s[x] + wit(1) }
	return g()
}

func pMapTargetMulti() int {
	m := map[int]int{}
	k := 1
	f := func() int { k = 2; return 1 }
	var y int
	m[k], y = 7, f()
	return m[1]*10 + m[2]*100 + y
}

func pForInit() int {
	s := []int{7, 8}
	r := 0
	for i := 0; i < 2; i++ {
		r += s[i] + wit(1)
	}
	return r
}

func pNew() int {
	p := new(int)
	s := []int{7}
	return s[*p] + wit(1)
}

func pAddrLit() int {
	s := []int{7}
	i := 0
	return (&T{n: s[i]}).n + wit(1)
}

func pMapLit() int {
	s := []int{7}
	i := 0
	return map[int]int{s[i]: 1}[7] + wit(1)
}

func pMake() int {
	s := []int{7}
	i := 0
	return len(make([]int, s[i])) + wit(1)
}

func main() {}

// the mS1 forgery through a TYPE-SWITCH binder: v is declared once in the source but the wire declares it per clause
// with the clause's type — the flat R1 table holds BOTH map types, so a forged annotation on the int-map clause's
// graph equal to the OTHER clause's type passes R1, and audit F1's base check compares against the annotation.
func pTypeSwitchMap() int {
	var iv interface{} = map[int]int{}
	r := 0
	switch v := iv.(type) {
	case map[int]int:
		r = v[1] + wit(1)
	case map[string]int:
		r = v["a"] + wit(2)
	}
	return r
}
