package main

// Close waking parked goroutines (ground-truth probes p24 and §3.4):
// a woken RECEIVER drains buffered values with ok=true then yields
// zeros with ok=false; a woken SENDER panics "send on closed channel"
// IN ITS OWN GOROUTINE, recoverably.

func closeWakesReceiver() int {
	ch := make(chan int)
	done := make(chan int)
	go func() {
		v, ok := <-ch // parks: open, empty
		if ok {
			done <- v
		} else {
			done <- 55
		}
	}()
	close(ch)
	return <-done
}

func closeWakesReceiverDrainFirst() int {
	ch := make(chan int, 2)
	ch <- 8
	done := make(chan int)
	go func() {
		a, okA := <-ch // buffered value first (ok=true), maybe pre- or post-close
		b, okB := <-ch // then closed-and-drained zero (ok=false)
		acc := a * 100
		if okA {
			acc += 10
		}
		acc += b
		if okB {
			acc += 1
		}
		done <- acc
	}()
	close(ch)
	return <-done
}

func closeWakesSenderPanics() (result int) {
	ch := make(chan int)
	done := make(chan int)
	go func() {
		defer func() {
			if recover() != nil {
				done <- 21 // the woken send's panic, recovered HERE
			} else {
				done <- 99
			}
		}()
		ch <- 1 // parks (unbuffered, no receiver); close wakes it into a panic
	}()
	close(ch)
	return <-done
}

func closeWakesSenderFullBuffer() int {
	ch := make(chan int, 1)
	ch <- 5
	done := make(chan int)
	go func() {
		defer func() {
			if recover() != nil {
				done <- 31
			} else {
				done <- 99
			}
		}()
		ch <- 6 // parks on the full buffer; close wakes it into a panic
	}()
	close(ch)
	got := <-done
	// The buffered value survives the close (close does not drain).
	return got*10 + <-ch
}

func main() {
	closeWakesReceiver()
	closeWakesReceiverDrainFirst()
	closeWakesSenderPanics()
	closeWakesSenderFullBuffer()
}
