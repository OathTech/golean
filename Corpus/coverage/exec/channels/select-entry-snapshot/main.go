package main

// Entry-time operand snapshot (spec#Select_statements step 1): ALL
// channel operands of receive clauses and BOTH the channel and the
// right-hand-side expression of send clauses are evaluated exactly
// once, in source order, on ENTRY to the select — a later clause's
// effectful operand mutating a variable an earlier clause's
// effect-free operand names must not change what the earlier clause
// communicates. BUG-074 ($GOROOT/test harvest 2026-09-01:
// fixedbugs/issue4313.go + issue43111.go): the lowering hoisted only
// EFFECTFUL operands to entry; effect-free ones were re-read at
// commit time, after the mutation.

// issue4313 shape: makec's entry-time hoist sets x = 42; the send
// value x must have been snapshotted at entry (0), not re-read at
// commit (42).
func selEntrySendValueSnapshot() int {
	c := make(chan int, 1)
	x := 0
	select {
	case c <- x:
	case <-makec(&x):
	}
	return <-c
}

func makec(px *int) chan int {
	*px = 42
	return nil
}

var snapCh chan int

func closeAndNil() int {
	close(snapCh)
	snapCh = nil
	return 1
}

// issue43111 shape: the second clause's RHS closes snapCh and sets it
// to nil at entry; the first clause's channel operand must be the
// entry-time (now closed, receivable) channel, not the re-read nil —
// re-reading deadlocks, the snapshot receives immediately.
func selEntryChanOperandSnapshot() int {
	snapCh = make(chan int)
	var nilch chan int
	select {
	case <-snapCh:
	case nilch <- closeAndNil():
	}
	return 7
}
