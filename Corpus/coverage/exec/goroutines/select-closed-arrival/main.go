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
	selectRecvClosedDrains()
	selectSendCloseRace()
	selectSendPairedThenClose()
}

// HB-ORDERED VARIANT (BUG-045 / arc-final audit F1): the racy
// reclassification above removes recv-parked-sender from the green
// lanes; this preserves its select-recv-on-closed drain/zero behavior
// RACE-FREE (probed: go build -race, 0 reports over 30 runs): main's
// own send is ordered before the child's close by the spawn edge, and
// the close before both selects by the done rendezvous — no parked
// sender exists. Returns 7100.
func selectRecvClosedDrains() int {
	ch := make(chan int, 1)
	ch <- 7
	done := make(chan int)
	go func() {
		close(ch)
		done <- 1
	}()
	<-done
	acc := 0
	select {
	case v, ok := <-ch:
		acc = v * 1000
		if ok {
			acc += 100
		}
	}
	acc2 := 0
	select {
	case w, ok2 := <-ch:
		acc2 = w * 10
		if ok2 {
			acc2 += 1
		}
	}
	return acc + acc2
}

// BUG-046 (convergence check on the BUG-045 fix): selectgo pass 1
// performs racereadpc on the CHANNEL OBJECT for every SEND case it
// polls (runtime/select.go:288, ABOVE the closed check) — the BUG-045
// fix's "selectgo bypasses chansend/closechan" premise was FALSE for
// send clauses — so a select-send clause racing a close is TSan-red
// exactly like a plain send (probed 30/30). Red-first pin; flips to
// PASS/racy when the detector's select-send poll read lands.
func selectSendCloseRace() int {
	ch := make(chan int)
	done := make(chan int)
	go func() {
		defer func() {
			if recover() != nil {
				done <- 21
			} else {
				done <- 99
			}
		}()
		select {
		case ch <- 7:
		}
	}()
	close(ch)
	return <-done
}

// The HB-ordered green twin (probed: go build -race, 0/30): main's
// receive PAIRS with the parked select-send (the op-x-select pairing),
// so the worker's poll read is ordered before main's close by the
// rendezvous — race-free on every schedule, and the shape exercises
// the select-send poll read plus a close on the same channel. 7.
func selectSendPairedThenClose() int {
	ch := make(chan int)
	go func() {
		select {
		case ch <- 7:
		}
	}()
	v := <-ch
	close(ch)
	return v
}
