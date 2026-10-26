package main

func main() { run() }

type T struct{ X int }

type I interface{ M() }

func (t *T) M() {}

type myErr struct{}

func (*myErr) Error() string { return "e" }

func mayFail(fail bool) error {
	var e *myErr
	if fail {
		e = &myErr{}
	}
	return e
}

func run() {
	var p *T
	var i any = p
	println(i == nil, i != nil, i == (*T)(nil), nil == i, i == any(p), i == any((*T)(nil)))
	var ii I = p
	println(ii == nil, ii == (*T)(nil), ii == I((*T)(nil)))
	var e error
	println(e == nil, e != nil)
	e = mayFail(false)
	println(e == nil, e == (*myErr)(nil))
	var f func()
	var fi any = f
	println(fi == nil, f == nil)
	var s []int
	var si any = s
	println(si == nil, s == nil)
	var m map[int]int
	var mi any = m
	println(mi == nil, m == nil)
	var c chan int
	var ci any = c
	println(ci == nil, c == nil, ci == (chan int)(nil), ci == any((<-chan int)(nil)))
	var j any
	println(j == nil, j == i, i == j)
	var k any = nil
	println(k == j)
	type P *int
	var pp P
	var pi any = pp
	println(pi == nil, pi == (P)(nil), pi == (*int)(nil))
}
