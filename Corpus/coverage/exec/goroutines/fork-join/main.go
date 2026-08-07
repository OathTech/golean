package main

// Fork/join basics (channels arc slice 2, D8): every subject is
// CONFLUENT — the observable is identical under every schedule, so the
// strict lane (go-run equality + three-stream invariance) applies at
// full strength.

func forkJoinUnbuffered() int {
	ch := make(chan int)
	go func() {
		ch <- 42
	}()
	return <-ch
}

func forkJoinBuffered() int {
	ch := make(chan int, 1)
	go func() {
		ch <- 7
	}()
	return <-ch * 10
}

func forkJoinCompute() int {
	ch := make(chan int)
	go func() {
		sum := 0
		for i := 1; i <= 10; i++ {
			sum += i
		}
		ch <- sum
	}()
	return <-ch
}

func forkJoinTwoWorkersOwnChans() int {
	a := make(chan int)
	b := make(chan int)
	go func() { a <- 3 }()
	go func() { b <- 4 }()
	// Distinct channels: each receive is pinned to its worker, so the
	// join order is deterministic regardless of schedule.
	return <-a*10 + <-b
}

// The go statement's function value and parameters are evaluated in the
// SPAWNING goroutine at the go statement (spec §Go statements): the
// mutation after `go` must not be visible to the worker's argument.
func goArgsEvalNow() int {
	ch := make(chan int)
	x := 1
	go func(v int) {
		ch <- v * 100
	}(x)
	x = 2
	return <-ch + x
}

func goClosureCapture() int {
	ch := make(chan int)
	base := 5
	go func() {
		// Captured by reference; the spawner blocks on the receive
		// until this runs, so no write races the read below.
		base = base + 1
		ch <- base * 10
	}()
	return <-ch
}

type adder struct {
	n int
}

func (a adder) addTo(ch chan int, v int) {
	ch <- a.n + v
}

// go with a method callee: the receiver and arguments are evaluated at
// the go statement in the spawning goroutine.
func goMethodCallee() int {
	ch := make(chan int)
	a := adder{n: 30}
	go a.addTo(ch, 9)
	a.n = 0
	return <-ch
}

// A goroutine's discarded results (spec: "If the function has any
// return values, they are discarded when the function completes").
func goResultDiscarded() int {
	ch := make(chan int)
	go func() int {
		ch <- 11
		return 99
	}()
	return <-ch
}

func main() {
	forkJoinUnbuffered()
	forkJoinBuffered()
	forkJoinCompute()
	forkJoinTwoWorkersOwnChans()
	goArgsEvalNow()
	goClosureCapture()
	goMethodCallee()
	goResultDiscarded()
}
