package main


type S struct{ p *int }

type E struct{}

func (E) Error() string { return "e" }

func f() {}

func both[T ~*int](t T) (bool, bool) { return nil == t, t == nil }

func probe() {
	var p *int
	var m map[int]int
	var sl []int
	var fn func()
	var ch chan int
	var i any
	var err error
	var s S
	x := 1
	q := &x
	println(nil == p, p == nil, nil != p, p != nil)
	println(nil == m, m == nil, nil == sl, sl == nil)
	println(nil == fn, fn == nil, nil == ch, ch == nil)
	println(nil == i, i == nil, nil == err, err == nil)
	println(nil == s.p, s.p == nil)
	println(nil == q, q == nil, nil != q, q != nil)
	fn = f
	err = E{}
	i = 3
	println(nil == fn, nil == err, nil == i, nil == (<-chan int)(ch))
	a, b := both(p)
	c, d := both(q)
	println(a, b, c, d)
	switch {
	case nil != p:
		println("switch: nil != p")
	case nil == p:
		println("switch: nil == p")
	}
	if nil == p && nil == m || nil != q {
		println("short-circuit ok")
	}
	println((nil == p) == (p == nil), (nil == q) == (q == nil))
	for nil == p {
		p = q
	}
	println(p == q)
}

func main() { probe() }
