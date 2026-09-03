package main

import "sync/atomic"

// THE ATOMIC SPIN-WAIT (atomics arc wave 1): the idiom class the arc
// exists for — a reader busy-waits on an atomic flag, then reads the
// data the writer published before setting it. Race-free (the
// load-acquire orders the plain read after the plain write — mem#atomic)
// and TERMINATING under any schedule that eventually runs the writer;
// on the always-spin schedules it never terminates. Per the [USER]
// ruling (A′, docs/2026-08-31_qrow-rulings.md row 2) the row is carried
// under `nonterm=` membership accounting with NO termination claim:
// the divergent branches are COUNTED, never members, and the
// Fair-quantified claim class that would license "terminates" is
// reasoning-side future work (proposal §2), not this repo's.

//
// SHAPE: main is the WRITER (plain data, then the atomic flag) and the
// spinner is a child goroutine reporting through a channel — so the
// canonical (issuer-continues) schedule terminates (main publishes,
// parks on the receive, the child observes the flag and reports), and
// the schedules that run the child before the store spin — the nonterm
// branches.
func spinOnFlag() int {
	var data int64
	var flag int32
	out := make(chan int64)
	go func() {
		for atomic.LoadInt32(&flag) == 0 {
		}
		out <- data
	}()
	data = 42
	atomic.StoreInt32(&flag, 1)
	return int(<-out) // 42 on every terminating path
}

func main() {
	spinOnFlag()
}
