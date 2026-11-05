package main

// Sweep lane sweep/s17-forms (2026-11-05), shape S17 (plan §4; the matrix
// on BUG-147's line): defer and go statements at the callee shapes the
// corpus did not hold — a struct field func, a slice element, a map
// element, a call's result, a dereferenced func pointer, a value- and a
// pointer-receiver method expression, an interface method, an explicit and
// an inferred generic instantiation, a spread call, and a defer / go inside
// a generic body. Expected = gc go1.26.5.

var calls int

type counter struct{ n int }

func (c *counter) inc()    { c.n++ }
func (c counter) bump()    { calls += c.n }
func (c *counter) send(ch chan int) { ch <- c.n }

type sender interface{ send(chan int) }

type holder struct {
	f func()
	g func(chan int)
}

func addG[T int | int64](x T) { calls += int(x) }

func sendG[T any](ch chan T, v T) { ch <- v }

func sum(xs ...int) int {
	for _, x := range xs {
		calls += x
	}
	return calls
}

// A9.2
func deferFieldFunc() int {
	calls = 0
	s := holder{f: func() { calls++ }}
	func() { defer s.f() }()
	return calls // 1
}

func deferSliceElemFunc() int {
	calls = 0
	fs := []func(){func() { calls += 2 }}
	func() { defer fs[0]() }()
	return calls // 2
}

func deferMapFunc() int {
	calls = 0
	m := map[int]func(){1: func() { calls += 3 }}
	func() { defer m[1]() }()
	return calls // 3
}

func deferCallOfCall() int {
	calls = 0
	mk := func() func() { calls += 10; return func() { calls += 4 } }
	func() {
		defer mk()() // mk runs at the defer statement, its result at exit
		calls *= 2
	}()
	return calls // (10*2)+4 = 24
}

func deferDerefFunc() int {
	calls = 0
	f := func() { calls += 5 }
	pf := &f
	func() { defer (*pf)() }()
	return calls // 5
}

// A9.3
func deferMethodExpr() int {
	calls = 0
	c := counter{n: 6}
	func() { defer counter.bump(c) }()
	return calls // 6
}

func deferPtrMethodExpr() int {
	c := &counter{}
	func() { defer (*counter).inc(c) }()
	return c.n // 1
}

// A9.4
func deferGenericExplicit() int {
	calls = 0
	func() { defer addG[int](3) }()
	return calls // 3
}

func deferGenericInferred() int {
	calls = 0
	func() { defer addG(int64(4)) }()
	return calls // 4
}

// A9.5
func deferSpread() int {
	calls = 0
	xs := []int{1, 2, 3}
	func() { defer sum(xs...) }()
	return calls // 6
}

// A9.9
func dG[T int | int64](x T) (r T) {
	defer func() { r += x }()
	return x
}

func deferInGeneric() int {
	return int(dG(5)) + int(dG(int64(1))) // 10 + 2 = 12
}

// A8.2
func goFieldFunc() int {
	done := make(chan int)
	s := holder{g: func(ch chan int) { ch <- 1 }}
	go s.g(done)
	return <-done // 1
}

func goSliceElemFunc() int {
	done := make(chan int)
	fs := []func(chan int){func(ch chan int) { ch <- 2 }}
	go fs[0](done)
	return <-done // 2
}

func goCallOfCall() int {
	done := make(chan int)
	mk := func() func(chan int) { return func(ch chan int) { ch <- 3 } }
	go mk()(done)
	return <-done // 3
}

func goDerefFunc() int {
	done := make(chan int)
	f := func(ch chan int) { ch <- 4 }
	pf := &f
	go (*pf)(done)
	return <-done // 4
}

// A8.3
func goMethodExpr() int {
	done := make(chan int)
	c := &counter{n: 5}
	go (*counter).send(c, done)
	return <-done // 5
}

func goIfaceMethod() int {
	done := make(chan int)
	var s sender = &counter{n: 6}
	go s.send(done)
	return <-done // 6
}

// A8.4
func goGenericExplicit() int {
	done := make(chan int)
	go sendG[int](done, 7)
	return <-done // 7
}

func goGenericInferred() int {
	done := make(chan string)
	go sendG(done, "abc")
	return len(<-done) // 3
}

// A8.8
func spawnG[T any](v T) T {
	ch := make(chan T)
	go func() { ch <- v }()
	return <-ch
}

func goInGeneric() int {
	return spawnG(8) + len(spawnG("xy")) // 10
}

func main() {
	println(deferFieldFunc(), deferSliceElemFunc(), deferMapFunc(), deferCallOfCall(), deferDerefFunc(),
		deferMethodExpr(), deferPtrMethodExpr(), deferGenericExplicit(), deferGenericInferred(), deferSpread(),
		deferInGeneric(), goFieldFunc(), goSliceElemFunc(), goCallOfCall(), goDerefFunc(), goMethodExpr(),
		goIfaceMethod(), goGenericExplicit(), goGenericInferred(), goInGeneric())
}
