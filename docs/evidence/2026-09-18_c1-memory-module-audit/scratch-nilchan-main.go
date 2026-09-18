package main

type S struct {
	c  chan int
	f  func() int
	cs [2]chan int
}

// &S{c: nil}: the composite literal's evaluated value reaches .allocNew with a raw nil in a chan slot
func allocNewNilChanField() int {
	p := &S{c: nil}
	r := 0
	if p.c == nil {
		r += 1
	}
	if len(p.c) == 0 && cap(p.c) == 0 {
		r += 2
	}
	q := &S{}
	if q.c == p.c {
		r += 4
	}
	return r
}

func allocNewNilChanArray() int {
	p := &S{cs: [2]chan int{nil, make(chan int, 1)}}
	r := 0
	if p.cs[0] == nil {
		r += 1
	}
	p.cs[1] <- 5
	r += <-p.cs[1]
	return r
}

func takeChan(c chan int) int {
	if c == nil {
		return 1
	}
	return 0
}

// bindParams: an untyped nil argument into a chan-typed parameter cell
func paramNilChan() int {
	return takeChan(nil)
}

// bindIterVars: range element cells of chan type holding nil
func iterNilChan() int {
	r := 0
	for i, c := range []chan int{nil, nil} {
		if c == nil {
			r += i + 1
		}
	}
	return r
}

// nil chan in a select with default
func selectNilChanField() int {
	p := &S{c: nil}
	select {
	case v := <-p.c:
		return v
	default:
		return 9
	}
}

// nil func field via &S{}, compared and then assigned
func allocNewNilFunc() int {
	p := &S{f: nil}
	r := 0
	if p.f == nil {
		r += 1
	}
	p.f = func() int { return 5 }
	return r + p.f()
}

// closure capturing a nil chan variable (captured cells are allocated too)
func captureNilChan() int {
	var c chan int
	g := func() bool { return c == nil }
	if g() {
		return 1
	}
	return 0
}

func main() {
	println(allocNewNilChanField(), allocNewNilChanArray(), paramNilChan(), iterNilChan(), selectNilChanField(), allocNewNilFunc(), captureNilChan())
}
