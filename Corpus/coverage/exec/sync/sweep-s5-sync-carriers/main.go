package main

// Defect-neighbourhood campaign, shape S5 (method sets: records, promotion,
// receiver adaptation, dispatch), lane sweep/s5-method-sets, 2026-10-27: every
// row is an agreement with gc on a route no earlier row held (the matrix is on
// the member entries' Neighbourhood lines in docs/BUGS.md; the plan is
// docs/2026-10-27_defect-neighbourhood-campaign.md §4).
// SYNC carriers beyond BUG-053's pins: the VALUE box of a primitive (an empty
// method set — every modeled method has a pointer receiver), a type switch
// with a user interface before `sync.Locker` over a `*sync.RWMutex`, the
// Lock/Unlock METHOD VALUES stored and called later, and a mutex embedded at
// depth 2 (the direct and deferred promoted calls, and satisfaction from the
// promoted stub record — dispatch THROUGH that record is the designed red
// embedding/promoted-stub-dispatch/box-sync-stub, at depth 1 already).

import "sync"

func valueBoxNoMethods() int {
	var mu sync.Mutex
	var x any = &mu
	_, okPtr := x.(sync.Locker)
	var y any = sync.Mutex{} // a fresh value: its method set is empty
	_, okVal := y.(sync.Locker)
	r := 0
	if okPtr {
		r += 1
	}
	if okVal {
		r += 10
	}
	return r
}

type rlocker interface {
	RLock()
	RUnlock()
}

func rwmutexTypeSwitch() int {
	classify := func(x any) int {
		switch x.(type) {
		case rlocker:
			return 1
		case sync.Locker:
			return 2
		default:
			return 3
		}
	}
	var rw sync.RWMutex
	var mu sync.Mutex
	a := classify(&rw)
	b := classify(&mu)
	c := classify(rw) // the value copy, boxed in its own statement: the unseq lane refuses it inside a multi-call expression (a hidden read of the sync word), by name
	return a*100 + b*10 + c
}

func lockMethodValues() int {
	var mu sync.Mutex
	lock := mu.Lock
	unlock := mu.Unlock
	n := 0
	lock()
	n++
	unlock()
	lock()
	n++
	unlock()
	return n
}

type guarded struct {
	sync.Mutex
	n int
}

type wrapper struct{ guarded }

func depth2EmbeddedMutex() int {
	var w wrapper
	w.Lock() // promoted two hops: (&w.guarded.Mutex).Lock()
	w.n++
	w.Unlock()
	defer w.Unlock()
	w.Lock()
	w.n++
	var x any = &w
	if _, ok := x.(sync.Locker); ok { // satisfaction answers from the promoted stub record
		w.n += 10
	}
	return w.n
}

func main() {
	valueBoxNoMethods()
	rwmutexTypeSwitch()
	lockMethodValues()
	depth2EmbeddedMutex()
}
