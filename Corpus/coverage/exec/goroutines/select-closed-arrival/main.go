package main

// A select ARRIVING at an already-closed channel that holds (or may
// hold) a parked partner (S2 convergence round, CRITICAL): gc checks
// closed BEFORE any waiter dequeue — chansend panics on closed
// unconditionally, chanrecv dequeues sendq only when not closed — so
// the arriving select must take the closed CELL semantics, never a
// pairing. Both subjects are confluent ACROSS schedules for exactly
// that reason (the waiter-blind pairing bug made some schedules
// deliver the parked partner's value instead).

// close(ch) precedes the select in main's program order, so the send
// clause panics under EVERY schedule — whether or not the worker's
// receive is already parked when the select arrives.
func selectSendClosedArrival() int {
	ch := make(chan int)
	go func() {
		v, ok := <-ch // zero/false (closed) — or parked until close wakes it
		_ = v
		_ = ok
	}()
	close(ch)
	select {
	case ch <- 3:
		return 103 // unreachable in Go: send on closed panics
	default:
		return 99 // unreachable: a send clause on closed counts as READY
	}
}

// The recv clause on a closed channel yields the drained zero with
// ok=false; the parked sender is woken by the close INTO its
// recoverable panic (probe p24) — it must never hand its value to the
// arriving select. Confluent: if the worker has not parked yet, its
// send hits the closed channel and panics identically.
func selectRecvClosedArrival() int {
	ch := make(chan int)
	done := make(chan int)
	go func() {
		defer func() {
			if recover() != nil {
				done <- 21 // send-on-closed, recovered (either timing)
			} else {
				done <- 99
			}
		}()
		ch <- 7
	}()
	close(ch)
	acc := 0
	select {
	case v, ok := <-ch:
		acc = v * 1000
		if ok {
			acc += 100
		}
	}
	return acc + <-done
}

func main() {
	selectSendClosedArrival()
	selectRecvClosedArrival()
}
