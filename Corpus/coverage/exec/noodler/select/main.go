// noodler probes — select/switch/channel edges (spec#Select_statements,
// spec#Switch_statements, spec#Close, spec#Receive_operator).
package main

// Only nil channels plus default: default.
func selectAllNilDefault() int {
	var a chan int
	var b chan string
	select {
	case <-a:
		return 1
	case b <- "x":
		return 2
	default:
		return 3
	}
}

// A nil channel beside a ready one: the ready one commits.
func selectNilBesideReady() int {
	var a chan int
	b := make(chan int, 1)
	b <- 4
	select {
	case v := <-a:
		return v
	case v := <-b:
		return v * 10
	}
}

// Closed channel in select: zero value, ok=false.
func selectClosedReceive() (int, bool) {
	c := make(chan int)
	close(c)
	select {
	case v, ok := <-c:
		return v, ok
	}
}

// Send on a closed channel via select panics.
func selectSendClosed() int {
	c := make(chan int, 1)
	close(c)
	select {
	case c <- 1:
		return 1
	}
}

// Select on only nil channels with no default: deadlock.
func selectAllNilDeadlock() int {
	var a chan int
	select {
	case <-a:
		return 1
	}
}

// Draining a closed buffered channel: buffered values then zeros.
func drainClosedBuffered() (int, int, bool) {
	c := make(chan int, 3)
	c <- 1
	c <- 2
	close(c)
	a := <-c
	b := <-c
	z, ok := <-c
	return a*10 + b, z, ok
}

// Range over a closed buffered channel yields the remaining values.
func rangeClosedBufferedSum() int {
	c := make(chan int, 4)
	for i := 1; i <= 4; i++ {
		c <- i
	}
	close(c)
	sum := 0
	for v := range c {
		sum += v
	}
	return sum
}

// Unlabeled break inside select inside for exits only the select.
func breakInSelectInFor() int {
	c := make(chan int, 5)
	for i := 0; i < 5; i++ {
		c <- i
	}
	n := 0
	for i := 0; i < 5; i++ {
		select {
		case <-c:
			n++
			break
		}
		n += 10
	}
	return n
}

// for-select with a labeled break after N receives.
func labeledBreakSelectLoop() int {
	c := make(chan int, 10)
	for i := 1; i <= 10; i++ {
		c <- i
	}
	sum := 0
loop:
	for {
		select {
		case v := <-c:
			sum += v
			if v == 4 {
				break loop
			}
		}
	}
	return sum
}

// Channel of channels.
func channelOfChannels() int {
	cc := make(chan chan int, 1)
	c := make(chan int, 1)
	cc <- c
	inner := <-cc
	inner <- 5
	return <-c
}

// Channel of funcs.
func channelOfFuncs() int {
	c := make(chan func(int) int, 1)
	c <- func(x int) int { return x * 3 }
	f := <-c
	return f(7)
}

// len/cap of a nil channel are 0; of a directional view they match.
func nilAndDirectionalLenCap() (int, int, int, int) {
	var n chan int
	c := make(chan int, 3)
	c <- 1
	var r <-chan int = c
	var s chan<- int = c
	return len(n) + cap(n), len(r), cap(s), len(c)
}

// Closed channel: a receive-side goroutine wakes with zero, false;
// reported through a second channel.
func closeWakesReceiver() (int, bool) {
	c := make(chan int)
	res := make(chan bool)
	go func() {
		_, ok := <-c
		res <- ok
	}()
	close(c)
	ok := <-res
	v, ok2 := <-c
	return v, ok || ok2
}

// Switch on a NaN tag: no case matches, even `case nan`.
func switchNaNTag() int {
	zero := 0.0
	nan := zero / zero
	switch nan {
	case nan:
		return 1
	case 0:
		return 2
	default:
		return 3
	}
}

// Switch on array values.
func switchArrayTag() int {
	a := [2]int{1, 2}
	switch a {
	case [2]int{2, 1}:
		return 1
	case [2]int{1, 2}:
		return 2
	}
	return 3
}

// Switch on struct values with an interface field.
func switchStructTag() int {
	type SI struct {
		n int
		i any
	}
	s := SI{1, "x"}
	switch s {
	case SI{1, 1}:
		return 1
	case SI{1, "x"}:
		return 2
	}
	return 3
}

// Duplicate runtime case values: the first matching case wins.
func switchDuplicateRuntimeCases() int {
	a, b := 3, 3
	switch 3 {
	case a:
		return 1
	case b:
		return 2
	}
	return 0
}

// Select with default only.
func selectDefaultOnly() int {
	select {
	default:
		return 9
	}
}

// Select on the same unbuffered channel for send and receive in one
// goroutine: neither can proceed, default fires.
func selectSelfSendRecvDefault() int {
	c := make(chan int)
	select {
	case c <- 1:
		return 1
	case <-c:
		return 2
	default:
		return 3
	}
}

// A receive on a closed channel of struct type yields the zero struct.
func closedStructChannelZero() (int, bool) {
	type SZ struct{ a, b int }
	c := make(chan SZ, 1)
	c <- SZ{1, 2}
	close(c)
	first := <-c
	z, ok := <-c
	return first.a + first.b + z.a + z.b, ok
}

// Unbuffered handoff between two goroutines in lockstep.
func pingPong() int {
	ping := make(chan int)
	pong := make(chan int)
	go func() {
		for v := range ping {
			pong <- v * 2
		}
		close(pong)
	}()
	sum := 0
	for i := 1; i <= 3; i++ {
		ping <- i
		sum += <-pong
	}
	close(ping)
	_, ok := <-pong
	if ok {
		return -1
	}
	return sum
}

// Switch with fallthrough into a default that sits in the middle.
func fallthroughIntoMiddleDefault(x int) int {
	r := 0
	switch x {
	case 1:
		r += 1
		fallthrough
	default:
		r += 10
	case 2:
		r += 100
	}
	return r
}

func main() {}
