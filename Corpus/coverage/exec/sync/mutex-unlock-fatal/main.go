package main

import "sync"

// Unlock of an unlocked mutex is an UNRECOVERABLE runtime throw in gc
// (probe p01: `fatal error: sync: unlock of unlocked mutex`, exit 2 —
// internal/sync.fatal, not a panic). Design note §2: modeled as the
// GoError.fatal terminal, never a recoverable panic.
func unlockOfUnlocked() int {
	var m sync.Mutex
	m.Unlock()
	return 0
}

// The recover discriminator (probe p01's exact shape): a deferred
// recover does NOT catch the throw — the run still aborts with the
// fatal. A model that raised a recoverable panic here would return 99.
func unlockRecoverAttempt() int {
	r := 0
	func() {
		defer func() {
			if recover() != nil {
				r = 99
			}
		}()
		var m sync.Mutex
		m.Unlock()
	}()
	return r
}

func main() {
	unlockOfUnlocked()
}
