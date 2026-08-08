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
	closeAfterSendDrains()
	sendOnClosedRecovered()
}

// HB-ORDERED VARIANTS (BUG-045 / arc-final audit F1): the racy
// reclassification above removes the close-beside-parked-SENDER
// subjects from the green lanes; these preserve their close-adjacent
// behavior coverage RACE-FREE (probed: go build -race, 0 reports over
// 30 runs each).

// The send completes and is ordered BEFORE the close (send -> done
// rendezvous -> close), so the chan-object read/write pair is
// HB-ordered: race-free. Behavior kept from closeWakesSenderFullBuffer:
// the buffered value survives the close and drains before the
// closed-zero. Returns 510.
func closeAfterSendDrains() int {
	ch := make(chan int, 1)
	done := make(chan int)
	go func() {
		ch <- 5   // completes: buffer room
		done <- 1 // orders the send before main's close
	}()
	<-done
	close(ch)
	v, ok := <-ch
	w, ok2 := <-ch
	acc := v * 100
	if ok {
		acc += 10
	}
	acc += w
	if ok2 {
		acc += 1
	}
	return acc
}

// The close is ordered BEFORE the send entry (close -> ready
// rendezvous -> send), so the send arrives on the closed channel and
// panics recoverably IN ITS OWN GOROUTINE — race-free (the read is
// HB-after the write). Behavior kept from closeWakesSenderPanics: the
// recoverable send-on-closed panic in a spawned goroutine, in its
// arrival form (the WAKE form is reachable only through a -race-red
// shape — see the cases.tsv note). Returns 21.
func sendOnClosedRecovered() int {
	ch := make(chan int)
	ready := make(chan int)
	done := make(chan int)
	go func() {
		defer func() {
			if recover() != nil {
				done <- 21
			} else {
				done <- 99
			}
		}()
		<-ready
		ch <- 1
	}()
	close(ch)
	ready <- 1
	return <-done
}
