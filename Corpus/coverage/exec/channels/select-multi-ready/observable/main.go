package main

// L2 ENTRY-PATH envelope pin (slice 4): a select with TWO ready cases
// whose arms are OBSERVABLY DISTINCT — the spec's "uniform pseudo-random
// selection" weakened to the possibilistic "any entry-ready case"
// (design of record D4). Single-goroutine on purpose: the only
// consumption site is the L2 clause pick (bound 2 — two ready clauses),
// so the enumerated set is exactly the two commits and the sequential
// enumerator certifies it without schedule exploration. Go's own
// runtime randomizes the pick (selectgo's cheaprandn shuffle), so the
// plain go-run sampler genuinely exercises both members.

func channelSelectMultiReadyObservable() int {
	a := make(chan int, 1)
	b := make(chan int, 1)
	a <- 1
	b <- 2
	got := 0
	select {
	case v := <-a:
		got = v
	case v := <-b:
		got = v
	}
	return got*100 + len(a)*10 + len(b)
}

func main() {
	println(channelSelectMultiReadyObservable())
}
