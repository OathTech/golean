// GoLean imported-goose corpus case — upstream bodies VERBATIM.
// source: testdata/examples/unittest/spawn.go @ 3be88bbb4982f58e5813b6f0344302d5582c8e8a
// imported: 2026-08-09 by scripts/import-goose
// transform: package clause -> main; assembly order as listed; all
// GoLean-authored code sits below the harness marker.
package main


import (
	"sync"
)

// Skip is a placeholder for some impure code
func Skip() {}

func simpleSpawn() {
	l := new(sync.Mutex)
	v := new(uint64)
	go func() {
		l.Lock()
		x := *v
		if x > 0 {
			Skip()
		}
		l.Unlock()
	}()
	l.Lock()
	*v = 1
	l.Unlock()
}

func threadCode(tid uint64) {}

func loopSpawn() {
	for i := uint64(0); i < 10; i++ {
		i := i
		go func() {
			threadCode(i)
		}()
	}
	for dummy := true; ; {
		// do some work to avoid a self-assignment
		dummy = !dummy
		continue
	}
}

// --- GoLean harness ---
// One int subject per upstream boolean oracle (true -> 1, false -> 0).

// Hand-authored (zero upstream oracles — the unittest wrapper lane):
// simpleSpawn completes whatever the child's schedule (the child may
// stay parked at main-exit — D6's unobservable leak). loopSpawn gets
// NO row: it is divergent BY DESIGN (`for dummy := true; ; { ... }`),
// the loops.go-demos precedent — probed before wrapping, per the
// buildout retrospective's lesson 3.
func goleanSimpleSpawn() int {
	simpleSpawn()
	return 1
}

func main() {}
