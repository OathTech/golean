package main

// Single-goroutine blocking shapes: every subject blocks with no other
// goroutine runnable, so Go's runtime deadlock detector fires
// ("fatal error: all goroutines are asleep - deadlock!", exit status 2).
// The machine models the blocked STATE; the sequential (slice-1) driver
// classifies any blocked configuration as the deadlocked terminal.
// NOTE (probed, ground-truth note §5): the detector does NOT fire under
// -race builds — deadlock-expectation cases must never run with -race.

func deadlockSendNil() int {
	var ch chan int
	ch <- 1
	return 0
}

func deadlockRecvNil() int {
	var ch chan int
	return <-ch
}

func deadlockSelectEmpty() int {
	select {}
}

func deadlockSelectAllNil() int {
	var a chan int
	var b chan bool
	select {
	case <-a:
		return 1
	case b <- true:
		return 2
	}
}

func deadlockSendUnbuffered() int {
	ch := make(chan int)
	ch <- 1
	return 0
}

func deadlockRecvEmptyOpen() int {
	ch := make(chan int, 2)
	return <-ch
}

func deadlockSendFull() int {
	ch := make(chan int, 1)
	ch <- 1
	ch <- 2
	return len(ch)
}

func deadlockRangeOpenDrained() int {
	ch := make(chan int, 2)
	ch <- 1
	ch <- 2
	sum := 0
	for v := range ch {
		sum += v
	}
	return sum
}

func main() {
	deadlockSendNil()
}
