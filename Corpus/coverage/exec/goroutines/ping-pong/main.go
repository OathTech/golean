package main

// Rendezvous ping-pong: unbuffered channels in both directions force
// strict alternation — every intermediate state is schedule-pinned.

func pingPong() int {
	ping := make(chan int)
	pong := make(chan int)
	go func() {
		for i := 0; i < 3; i++ {
			v := <-ping
			pong <- v + 1
		}
	}()
	acc := 0
	for i := 0; i < 3; i++ {
		ping <- acc * 2
		acc = <-pong
	}
	return acc
}

// cap=0 make(chan int, 0) is the same unbuffered rendezvous (one spec
// rule, probe p11) — across goroutines this time.
func pingPongCapZero() int {
	ch := make(chan int, 0)
	done := make(chan int)
	go func() {
		got := <-ch
		done <- got * 3
	}()
	ch <- 14
	return <-done
}

func main() {
	pingPong()
	pingPongCapZero()
}
