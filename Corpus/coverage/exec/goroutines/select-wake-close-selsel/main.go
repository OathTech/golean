package main

// The C7 close-wake MEMBERSHIP pin (audit fix round 2026-09-01, C8;
// corpus twin of the evidence probe
// docs/evidence/2026-09-01_c7-close-wake-probe/probe/main.go): a
// select parked with TWO recv clauses on ONE channel, woken by
// close(ch) from another goroutine — one waking event, width-2
// wake-readiness. gc commits EITHER clause (~half each in the probe's
// 200-run-per-config counts: selectgo builds lockorder from the
// shuffled pollorder precisely to permute same-channel cases), so the
// case is cheap and implementation-independent: any conforming
// implementation may realize both. Machine certified set {1, 2}
// (members=2): clause 1 via the wake head-commit; clause 2 via the
// always-realizable close-before-entry schedule + the entry-path L2
// draw. This is exactly the corner that falsified C7's old
// commit-by-waking-event wording (the two-leg argument of record:
// inventory C7 + §8 e12).
//
// Race note: receiver-side close wake — recv is acquire-only at the
// chan object (the BUG-045 classification), so this shape is
// TSan-green, unlike the parked-SENDER close shapes.

func selectWakeCloseSelsel() int {
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
	println(selectWakeCloseSelsel())
}
