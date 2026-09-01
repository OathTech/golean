package main

import "sync"

// LIFTED (Q-SYNCLIT, [USER]-RULED 2026-08-31; implemented on the
// Q-SYNCVAL slice 2026-09-01; formerly PERMANENT-until-lifted refusal
// markers from the arc-end fix round 2026-08-10): composite-literal
// CONSTRUCTION of a modeled sync primitive. The semantics is FORCED —
// spec#Composite_literals makes any element for a non-exported field
// illegal cross-package, and all four primitives have only
// non-exported fields, so the entire legal literal surface is the
// EMPTY literal ≡ the zero value ≡ what `var`/`new` construct ("The
// zero value for a Mutex is an unlocked mutex", sync docs). The COPY
// half is answered by the sync design (§3, probe p10): sync state is
// modeled as VALUES and copies carry state, gc-faithfully. Non-empty
// sync literals keep failing closed (unreachable cross-package).
func mutexAddrLit() int {
	m := &sync.Mutex{}
	m.Lock()
	x := 7
	m.Unlock()
	return x
}

func waitGroupValueLit() int {
	wg := sync.WaitGroup{}
	wg.Add(1)
	wg.Done()
	wg.Wait()
	return 3
}

// The remaining two primitives' literal forms (gc: 5 / 2).
func rwMutexAddrLit() int {
	rw := &sync.RWMutex{}
	rw.RLock()
	x := 5
	rw.RUnlock()
	return x
}

func onceValueLit() int {
	o := sync.Once{}
	n := 0
	o.Do(func() { n += 2 })
	o.Do(func() { n += 9 })
	return n
}

// Sync literal NESTED IN a composite (audit fix round 2026-09-01,
// F10): the empty sync literal in ELEMENT position — a slice of
// mutexes and an explicit struct-field literal — pins that the
// zero-value lowering holds inside enclosing composites, not just
// standalone.
type guardedCell struct {
	mu sync.Mutex
	n  int
}

func syncLitInComposite() int {
	ms := []sync.Mutex{{}, {}}
	ms[0].Lock()
	ms[1].Lock()
	ms[0].Unlock()
	ms[1].Unlock()
	g := guardedCell{mu: sync.Mutex{}, n: 4}
	g.mu.Lock()
	g.n += 2
	g.mu.Unlock()
	return g.n
}

func main() {
	mutexAddrLit()
}
