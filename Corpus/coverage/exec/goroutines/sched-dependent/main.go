package main

// SCHEDULE-DEPENDENT observables — deliberately RED-PINNED for slice 4
// (charter: the membership lane's enumerator over schedules). The
// observation genuinely varies with the schedule (which sender commits
// first is pure L1 latitude), so the strict lane's three-stream
// invariance check must refuse it; the membership lane will own it.

func schedFirstCome() int {
	ch := make(chan int, 2)
	done := make(chan int)
	go func() {
		ch <- 1
		done <- 0
	}()
	go func() {
		ch <- 2
		done <- 0
	}()
	<-done
	<-done
	first := <-ch
	second := <-ch
	return first*10 + second // 12 or 21, by schedule
}


// Select-with-default against a maybe-parked partner (S2 audit, major
// finding: waiter-blind select readiness): whether the worker has
// PARKED at its send before main's select decides is pure L1 latitude,
// so the observation set is {7, 99} — go1.26.5 measured 199970/30 over
// 200000 runs (audit verifier probe). The waiter-aware readiness fix
// makes 7 reachable in the model; schedule enumeration (slice 4) owns
// certifying the set.
func schedSelectDefaultHandshake() int {
	ready := make(chan int)
	ch := make(chan int)
	go func() {
		ready <- 1
		ch <- 7
	}()
	<-ready
	select {
	case v := <-ch:
		return v
	default:
		return 99
	}
}

// Buffer-occupancy observation with a maybe-parked receiver (S2 audit,
// major finding: buffered sends bypassed parked waiters): if the
// worker is parked at its receive when main's send arrives, gc hands
// off DIRECTLY (len stays 0); if the worker has not arrived, the send
// buffers (len 1 until the worker drains). The observation set is
// {100, 110}; only the waiter-priority model reaches gc's dominant
// handoff outcome. Schedule enumeration (slice 4) owns the set.
func schedLenHandoff() int {
	ready := make(chan int)
	ch := make(chan int, 2)
	done := make(chan int)
	go func() {
		ready <- 1
		v := <-ch
		done <- v
	}()
	<-ready
	ch <- 1
	l := len(ch)
	r := <-done
	return r*100 + l*10
}

func main() {
	schedFirstCome()
	schedSelectDefaultHandshake()
	schedLenHandoff()
}
