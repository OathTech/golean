package main

// The main-exit WINDOW (channels-arc final audit F2, BUG-044): after a
// registry op of main's wakes a partner (a pairing handoff, a close),
// gc may run the woken goroutine any finite amount BEFORE main's exit
// tears the program down (spec §Program execution gives no ordering
// between main's return and other goroutines' progress). Both subjects
// are RACE-FREE (go build -race: zero reports over 30 runs each,
// probed 2026-08-08) and their envelope is status-diverse {ok, panic}:
// plain gc realizes ok (and, with a private delay loop after the wake,
// the panic — dossier probe n50000); the -race runtime's scheduling
// perturbation realizes the panic member 40/40. A model without a
// scheduling point between the wake and main's terminal certifies the
// singleton {ok} and excludes a member the oracle exhibits — the
// too-narrow direction that breaks theorem transfer.

// The pairing-wake shape (dossier probe g): main's buffered send wakes
// the parked receiver; the woken goroutine's continuation panics; main
// exits with 0. gc realizes both program outcomes.
func bufSendWakeThenExit() int {
	ch := make(chan int, 1)
	ready := make(chan int)
	go func() {
		ready <- 1
		<-ch
		panic("receiver ran")
	}()
	<-ready
	ch <- 1
	return 0
}

// The close-wake shape at the same boundary: main's close wakes the
// parked receiver (recv is acquire-only at the channel object, so the
// close-beside-parked-RECEIVER family is TSan-green — unlike the
// parked-sender family, which is the racy-negative lane's).
func closeWakeReceiverThenExit() int {
	ch := make(chan int)
	ready := make(chan int)
	go func() {
		ready <- 1
		<-ch
		panic("woken receiver ran")
	}()
	<-ready
	close(ch)
	return 0
}

func main() {
	bufSendWakeThenExit()
	closeWakeReceiverThenExit()
}
