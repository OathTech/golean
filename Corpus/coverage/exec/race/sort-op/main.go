package main

// The `sortSlice` MACHINE OP's write set against the race detector
// (BUG-131; review of lane frontend/g19-sort-intercept-1025, F1,
// 2026-10-25). The op records EVERY window element as read then WRITTEN
// (Machine.lean, the `.sortSlice` apply arm), where gc's pdqsort on an
// already-ordered window performs NO write (`insertionSortOrdered` swaps
// only out-of-order neighbours). So a concurrent READ of a sorted slice
// while the op sorts it is refused `race` by the machine where
// `go run -race` is green and the program's answer is determined: an
// OVER-REFUSAL (the machine refuses ⊇ gc), a status-level differential
// observation — the FAIL row below pins the class, expected `ok`. The
// write set is NOT narrowed to the changed elements: pdqsort may write an
// element it leaves in place (a swap chain through it), and a missed
// write would be a false `ok` — the unsound direction. raft's sorts are
// on local temporaries (CommittedIndex's stack array, Visit's/Slice's
// fresh slices), never shared: unaffected.

import "slices"

// RED PIN (BUG-131): the direct call `slices.Sort(s)` inside the spawned
// closure is the op (expression-statement position); the sibling reads
// s[0]; both join main through the channel before the readout, so gc's
// answer is the one value 1123 and gc -race reports nothing (no write).
func sortedWindowConcurrentRead() int {
	s := []int{1, 2, 3}
	seen := 0
	done := make(chan int, 2)
	go func() {
		slices.Sort(s)
		done <- 0
	}()
	go func() {
		seen = s[0]
		done <- 0
	}()
	<-done
	<-done
	return seen*1000 + s[0]*100 + s[1]*10 + s[2]
}

// GREEN CONTROL: the same program with `go slices.Sort(s)` — the spawned
// FUNCTION VALUE is the real generic (the intercept is statement-position
// only), whose insertion sort of the ordered window reads and never
// writes, so the machine's detector agrees with gc: race-free.
func sortedWindowConcurrentReadGeneric() int {
	s := []int{1, 2, 3}
	seen := 0
	done := make(chan int, 2)
	go slices.Sort(s)
	go func() {
		seen = s[0]
		done <- 0
	}()
	<-done
	return seen*1000 + s[0]*100 + s[1]*10 + s[2]
}
