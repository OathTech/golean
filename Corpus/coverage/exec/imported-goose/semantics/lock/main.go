// GoLean imported-goose corpus case — upstream bodies VERBATIM.
// source: testdata/examples/semantics/lock.go @ 3be88bbb4982f58e5813b6f0344302d5582c8e8a
// imported: 2026-08-09 by scripts/import-goose
// transform: package clause -> main; assembly order as listed; all
// GoLean-authored code sits below the harness marker.
package main


import "sync"

// We can't interpret multithreaded code, so this just checks that
// locks are correctly interpreted
func testsUseLocks() bool {
	m := new(sync.Mutex)
	m.Lock()
	m.Unlock()
	return true
}

// --- GoLean harness ---
// One int subject per upstream boolean oracle (true -> 1, false -> 0).

func goleanTestsUseLocks() int {
	if testsUseLocks() {
		return 1
	}
	return 0
}

func main() {}
