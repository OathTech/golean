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

// ARC-END pin (2026-08-10): the fatal raised DURING PANIC UNWINDING —
// the idiomatic `defer m.Unlock()` in a panicking frame. gc's abort
// LEADS with `panic: boom` and carries the fatal on a TAB-INDENTED
// continuation line (`\tfatal error: sync: unlock of unlocked mutex`),
// exit 2 — so the harness extractor must accept the indented shape.
// The model reports the fatal (class and message gc-exact) but DROPS
// the pending panic value from its observation — a recorded narrowing
// (design note §8), not compared here.
func unlockDuringUnwind() int {
	var m sync.Mutex
	defer m.Unlock()
	panic("boom")
}

func main() {
	unlockOfUnlocked()
}
