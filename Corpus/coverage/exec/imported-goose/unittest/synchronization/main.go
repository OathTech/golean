// GoLean imported-goose corpus case — upstream bodies VERBATIM.
// source: testdata/examples/unittest/synchronization.go @ 3be88bbb4982f58e5813b6f0344302d5582c8e8a
// imported: 2026-08-09 by scripts/import-goose
// transform: package clause -> main; assembly order as listed; all
// GoLean-authored code sits below the harness marker.
// imports-allowed: sync (--allow-import)
package main


import "sync"

// DoSomeLocking uses the entire lock API
func DoSomeLocking(l *sync.Mutex) {
	l.Lock()
	l.Unlock()
	// l.RLock()
	// l.RLock()
	// l.RUnlock()
	// l.RUnlock()
}

func makeLock() {
	l := new(sync.Mutex)
	DoSomeLocking(l)
}

// --- GoLean harness ---
// One int subject per upstream boolean oracle (true -> 1, false -> 0).

// Hand-authored (zero upstream oracles — the unittest wrapper lane):
// exercise the whole upstream lock API surface and report completion.
func goleanMakeLock() int {
	makeLock()
	DoSomeLocking(new(sync.Mutex))
	return 1
}

func main() {}
