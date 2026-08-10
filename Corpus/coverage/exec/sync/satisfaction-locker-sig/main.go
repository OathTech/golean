package main

import "sync"

// ARC-END fix-round pin (2026-08-10), split from sync/satisfaction:
// a satisfaction query whose interface literal MENTIONS sync.Locker
// (RLocker's result type). Before the fix the mere mention of
// sync.Locker refused the WHOLE export ("sync.Locker (only
// Mutex/RWMutex/WaitGroup/Once are modeled)") — kept in its own file
// so that refusal cannot mask the silent-wrong-answer reds pinned in
// sync/satisfaction. RLocker itself is never CALLED (calls stay
// quarantined per-stub).
func assertOkRWMutex() int {
	var rw sync.RWMutex
	var i any = &rw
	if _, ok := i.(interface {
		RLock()
		RUnlock()
		RLocker() sync.Locker
	}); ok {
		return 51
	}
	return 0
}

func main() {
	assertOkRWMutex()
}
