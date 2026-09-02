package main

// E9 cross-goroutine delete-prune — the OVER-PRUNE guards (E9-prune
// audit fix round F5, 2026-09-02 [AGENT]). The sibling package
// cross-goroutine-delete-readd catches UNDER-pruning (a foreign prune
// that does not reach the ranging goroutine's frame leaves its
// membership sets singletons — the lint's honest red). Nothing there
// catches a prune that reaches TOO FAR: one that empties the ranging
// goroutine's start set on a plain delete (making an early stop legal),
// or one that ignores map identity (pruning a key out of a range over a
// DIFFERENT map, so an already-produced key re-enters as a candidate).
// The three rows here are schedule-CONFLUENT: exactly one observable is
// legal under the spec's production table, so a widened enumerated set
// is red. Every map access is HB-ordered by the req/ack handshake (the
// drf row's shape; `go run -race` green), so the racy lane never
// engages and a widened set can only be the prune.
//
// spec#For_statements (range clause, maps): "If a map entry that has
// not yet been reached is removed during iteration, the corresponding
// iteration value will not be produced." Deleting an ALREADY-produced
// key (with no re-create) changes nothing the range can observe: the
// remaining start keys are still mandatory (never removed), the deleted
// one cannot be a candidate (it is not live), and no entry is created.

// (a) Cross-goroutine delete of the first-produced key, NO re-add:
// n = 3 productions, sum of produced keys = 6 → 3006, uniquely. An
// over-prune that empties the ranging frame's START set makes a stop
// legal after 1 or 2 productions (widening to {1xxx, 2xxx, 3006}); an
// under-prune leaves the observable unchanged (the deleted key was
// produced already and is not live) — this row is the over-prune guard.
func crossGoroutineDeleteNoReAdd() int {
	m := map[int]int{1: 1, 2: 2, 3: 3}
	req := make(chan int)
	ack := make(chan int)
	go func() {
		k := <-req
		delete(m, k)
		ack <- 0
	}()
	n := 0
	sum := 0
	first := true
	for k := range m {
		n++
		sum += k
		if first {
			first = false
			req <- k
			<-ack
		}
	}
	return n*1000 + sum
}

// (b) Cross-goroutine clear(m) mid-range: after the first production
// the other goroutine clears the map; no live entry remains, so the
// range ends with exactly 1 production. The observable is fixed under
// EVERY prune (nothing is left to produce and nothing is created); the
// row pins that a foreign clear neither refuses nor produces a stale
// entry.
func crossGoroutineClearMidRange() int {
	m := map[int]int{1: 1, 2: 2, 3: 3}
	req := make(chan int)
	ack := make(chan int)
	go func() {
		<-req
		clear(m)
		ack <- 0
	}()
	n := 0
	first := true
	for k := range m {
		n++
		if first {
			first = false
			req <- k
			<-ack
		}
	}
	return n
}

// (c) Map IDENTITY: goroutine A ranges m1 while B deletes the
// handed-over key from m2 (a different map with the same key set). m1's
// range is untouched: 3 productions, sum 6 → 3006, uniquely. An
// over-prune that ignores the map base would drop k from m1's produced
// set, making the still-live k a candidate again (widening to {3006,
// 4006+k}).
func crossGoroutineDeleteOtherMap() int {
	m1 := map[int]int{1: 1, 2: 2, 3: 3}
	m2 := map[int]int{1: 1, 2: 2, 3: 3}
	req := make(chan int)
	ack := make(chan int)
	go func() {
		k := <-req
		delete(m2, k)
		ack <- 0
	}()
	n := 0
	sum := 0
	first := true
	for k := range m1 {
		n++
		sum += k
		if first {
			first = false
			req <- k
			<-ack
		}
	}
	return n*1000 + sum
}

func main() {
	println(crossGoroutineDeleteNoReAdd())
	println(crossGoroutineClearMidRange())
	println(crossGoroutineDeleteOtherMap())
}
