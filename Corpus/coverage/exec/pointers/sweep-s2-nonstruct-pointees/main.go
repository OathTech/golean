package main

// Defect-neighbourhood campaign, shape S2 (conversions: a missing kernel arm or a
// value not retagged), lane sweep/s2-conversions, 2026-10-26: every row is an
// agreement with gc on a route no earlier row held (the matrix is on the member
// entries' Neighbourhood lines in docs/BUGS.md; the plan is
// docs/2026-10-27_defect-neighbourhood-campaign.md §4).
// Pointer conversions whose pointee is a defined NON-struct type (float, string,
// bool, slice, map, func, chan, array, interface): derefRetag's resolve yields a
// plain body, the value is untouched, the box takes the STATIC type; plus a
// defined pointer type and a pointer to a pointer (train-20 audit p16 covers the
// int pointee).

type MyFloat float64
type MyStr string
type MyBool bool
type MyInts []int
type MyMap map[string]int
type MyFn func() int
type MyChan chan int
type Arr [2]int
type Brr [2]int
type MyIface interface{ M() int }
type A struct{ X int }
type PA *A

func kindOf(i any) int {
	switch i.(type) {
	case float64:
		return 1
	case MyFloat:
		return 2
	case string:
		return 3
	case MyStr:
		return 4
	case bool:
		return 5
	case MyBool:
		return 6
	case []int:
		return 7
	case MyInts:
		return 8
	case map[string]int:
		return 9
	case MyMap:
		return 10
	case func() int:
		return 11
	case MyFn:
		return 12
	case chan int:
		return 13
	case MyChan:
		return 14
	case Arr:
		return 15
	case Brr:
		return 16
	}
	return 0
}

func derefFloatPointee() (int, bool) {
	f := 1.5
	p := (*MyFloat)(&f)
	*p = *p * 2
	var i any = *p
	return kindOf(i), f == 3.0
}

func derefStringPointee() (int, string) {
	s := "ab"
	p := (*MyStr)(&s)
	*p += "c"
	var i any = *p
	return kindOf(i), s
}

func derefBoolPointee() (int, bool) {
	b := false
	p := (*MyBool)(&b)
	*p = true
	var i any = *p
	return kindOf(i), b
}

func derefSlicePointee() (int, int, int) {
	s := []int{1, 2}
	p := (*MyInts)(&s)
	*p = append(*p, 3)
	(*p)[0] = 9
	var i any = *p
	return kindOf(i), len(s), s[0]
}

func derefMapPointee() (int, int) {
	m := map[string]int{"a": 1}
	p := (*MyMap)(&m)
	(*p)["b"] = 2
	*p = MyMap{"c": 3}
	var i any = *p
	return kindOf(i), len(m)*10 + m["c"]
}

func derefFuncPointee() (int, int) {
	f := func() int { return 4 }
	p := (*MyFn)(&f)
	*p = func() int { return 5 }
	var i any = *p
	return kindOf(i), f() + (*p)()
}

func derefChanPointee() (int, int) {
	c := make(chan int, 1)
	p := (*MyChan)(&c)
	*p <- 7
	var i any = *p
	return kindOf(i), <-c
}

func derefArrayPointee() (int, int) {
	a := Arr{1, 2}
	p := (*Brr)(&a)
	p[0] = 5
	*p = Brr{7, 8}
	var i any = *p
	return kindOf(i), a[0]*10 + a[1]
}

func (a A) M() int { return a.X }

func derefIfacePointee() (int, int) {
	var j interface{ M() int } = A{3}
	p := (*MyIface)(&j)
	*p = A{4}
	return (*p).M(), j.M()
}

func definedPointerType() int {
	a := A{1}
	p := PA(&a)
	p.X = 2
	q := (*A)(p)
	q.X++
	var i any = p
	r := 0
	switch i.(type) {
	case *A:
		r = 1
	case PA:
		r = 2
	}
	return r*10 + a.X
}

func pointerToPointer() int {
	a := A{1}
	pa := &a
	pp := (*PA)(&pa)
	(*pp).X = 5
	b := A{9}
	*pp = &b
	return a.X*10 + pa.X
}

func main() {}
