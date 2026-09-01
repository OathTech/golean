package main

// C7 close-wake probe (2026-09-01, the A1-14 unprobed corner): a select
// parked with TWO recv clauses on ONE channel, woken by close(ch) from
// another goroutine — ONE waking event, width-2 wake-readiness. The
// C7 (b-n) narrowing's recorded argument ("a parked gc select is
// committed by the EVENT that wakes it") predicts a deterministic
// commit here; gc's selectgo pollorder shuffle predicts either clause.
// Observable: which clause body runs, returned and printed.
//
// Race note: receiver-side close wake — recv is acquire-only at the
// chan object (the BUG-045 classification), so this shape is
// TSan-green, unlike the parked-SENDER close shapes.

func selselCloseWake() int {
	ch := make(chan int)
	done := make(chan int)
	go func() {
		close(ch)
		done <- 1
	}()
	got := 0
	select {
	case <-ch:
		got = 1
	case <-ch:
		got = 2
	}
	<-done
	return got
}

func main() {
	println(selselCloseWake())
}
