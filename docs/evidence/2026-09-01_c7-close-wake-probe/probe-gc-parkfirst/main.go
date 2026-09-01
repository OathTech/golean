package main

// gc-ONLY park-first variant of the C7 close-wake probe (2026-09-01):
// the closer sleeps 2ms before close(ch), making "main's select is
// PARKED before the close runs" near-certain on every GOMAXPROCS —
// this isolates the WAKE path from the entry path (a close landing
// before select entry would exercise the entry-time uniform choice,
// C6's already-enveloped site, not C7's wake commit). Not a machine
// subject (time.Sleep is outside the modeled surface); the plain
// ../probe/main.go is the shared machine/gc subject.

import "time"

func selselCloseWakeParkFirst() int {
	ch := make(chan int)
	done := make(chan int)
	go func() {
		time.Sleep(2 * time.Millisecond)
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
	println(selselCloseWakeParkFirst())
}
