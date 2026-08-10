package main

import "sync"

// RWMutex Unlock without a held write lock: unrecoverable runtime
// throw (probe p02: `fatal error: sync: Unlock of unlocked RWMutex`,
// exit 2). Holding only a READ lock does not license Unlock.
func wunlockOfUnlocked() int {
	var m sync.RWMutex
	m.Unlock()
	return 0
}

// RUnlock without a held read lock: unrecoverable runtime throw
// (probe p03: `fatal error: sync: RUnlock of unlocked RWMutex`).
func runlockOfUnlocked() int {
	var m sync.RWMutex
	m.RUnlock()
	return 0
}

// RUnlock while WRITE-locked is the same unrecoverable throw (audit
// fix round F5 — probed, previously unpinned): readers = 0 under a
// held write lock, so the misuse classifies identically.
func runlockWhileWriteLocked() int {
	var m sync.RWMutex
	m.Lock()
	m.RUnlock()
	return 0
}

func main() {
	wunlockOfUnlocked()
}
