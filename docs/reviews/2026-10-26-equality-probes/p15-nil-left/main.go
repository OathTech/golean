package main

func main() { run() }

func run() {
	x := 1
	p := &x
	var np *int
	println(nil == p, nil != p, nil == np, nil != np)
	m := map[int]int{}
	var nm map[int]int
	println(nil == m, nil == nm, nil != nm)
	s := []int{}
	var ns []int
	println(nil == s, nil == ns, nil != ns)
	f := func() {}
	var nf func()
	println(nil == f, nil == nf, nil != f)
	var i any = 1
	var ni any
	println(nil == i, nil == ni, nil != ni)
	ch := make(chan int)
	var nch chan int
	println(nil == ch, nil == nch, nil != nch)
	var e error
	println(nil == e, e == nil)
	if nil == p {
		println("unreachable")
	}
	switch {
	case nil == np:
		println("nil-left in switch")
	}
	println(p != nil && *p == 1)
}
