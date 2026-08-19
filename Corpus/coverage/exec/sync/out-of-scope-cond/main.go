package main

import "sync"

// PERMANENT-until-lifted refusal marker (design note §9, D4:
// sync.Cond is OUT of slice-2 scope): a Signal with no waiter is a
// no-op, so the go side runs clean — the case is red at
// frontend-export by design until a Cond slice lifts it.
func condSignalNoWaiter() int {
	var m sync.Mutex
	c := sync.NewCond(&m)
	c.Signal()
	return 1
}

// Slice-6 additions (the whole-language bar): the Cond design
// question's cases-in-hand (ledger Q-COND — the wakeup envelope:
// which waiter Signal picks, Broadcast ordering, the spurious-wakeup
// question the loop-recheck idiom absorbs). Both observables are
// deterministic ACROSS the envelope: one waiter (Signal) and
// sum-of-two (Broadcast) normalize the wakeup order away, so a strict
// pin stays honest for any conforming Cond model. Red at
// frontend-export by design (the wire.go sync.Cond refusal) until a
// Cond slice.

func condWaitSignal() int {
	var mu sync.Mutex
	c := sync.NewCond(&mu)
	ready := false
	done := make(chan int)
	go func() {
		mu.Lock()
		for !ready {
			c.Wait()
		}
		mu.Unlock()
		done <- 8
	}()
	mu.Lock()
	ready = true
	c.Signal()
	mu.Unlock()
	return <-done // 8 (signal-before-wait and wait-before-signal both land here)
}

func condBroadcast() int {
	var mu sync.Mutex
	c := sync.NewCond(&mu)
	released := 0
	done := make(chan int)
	for i := 0; i < 2; i++ {
		go func() {
			mu.Lock()
			for released == 0 {
				c.Wait()
			}
			mu.Unlock()
			done <- 3
		}()
	}
	mu.Lock()
	released = 1
	c.Broadcast()
	mu.Unlock()
	return <-done + <-done // 6, wakeup order normalized away
}

func main() {
	condSignalNoWaiter()
	condWaitSignal()
	condBroadcast()
}
