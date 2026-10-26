package main

// A converted pointer sent on chan *B and received in another goroutine,
// which dereferences it whole and sends the value back on chan B.
type A struct{ X, Y int }
type B struct{ X, Y int }

func probe() int {
	a := A{1, 2}
	cp := make(chan *B, 1)
	cv := make(chan B)
	go func() {
		p := <-cp
		cv <- *p
	}()
	cp <- (*B)(&a)
	v := <-cv
	if v == (B{1, 2}) {
		return 1
	}
	return 0
}

func main() { println(probe()) }
