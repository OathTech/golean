package main

import "sync"

// The F4 stub's REGRESSION PIN (delta-review round 2): interface
// satisfaction on a struct embedding a sync primitive answers YES
// through the declaration-only quarantined stubs (promoted Lock/Unlock
// enter the method table; their bodies refuse if called). A frontend
// change that drops or mis-shapes the stubs flips this to a false "no"
// (0) with status ok — the silent regression the delta-review verifier
// exhibited with a stub-dropping frontend build. No promoted method is
// CALLED here (calls are the recorded out-of-scope escape class).
type lockerBox struct {
	sync.Mutex
	n int
}

type locker interface {
	Lock()
	Unlock()
}

func stubSatisfaction() int {
	var b lockerBox
	b.n = 4
	var i any = &b
	if _, ok := i.(locker); ok {
		return b.n
	}
	return 0
}

func main() {
	stubSatisfaction()
}
