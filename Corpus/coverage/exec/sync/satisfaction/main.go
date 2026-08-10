package main

import "sync"

// ARC-END fix-round pins (2026-08-10): interface SATISFACTION on the
// four modeled sync primitives must answer what gc answers. The S2
// design minted satisfaction stubs only for methods PROMOTED into a
// user struct (sync/stub-satisfaction); the base capability — a bare
// `*sync.Mutex` satisfying a Lock/Unlock-shaped interface, which is
// `sync.Locker`'s whole reason to exist — answered a false "no": the
// wrong comma-ok bool and type-switch branch with status ok, and a
// spurious "missing method" panic on a bare assert gc completes
// (verifier-reproduced end-to-end). Red-first: every subject below is
// go-run-verified and red before the frontend stub fix. No sync method
// is CALLED through an interface here (that shape's markers live in
// sync/iface-dispatch).

type locker interface {
	Lock()
	Unlock()
}

// fooLocker requires a method no sync primitive has: the DEFINITE-no
// side must stay a real "no" once the method set is on the wire.
type fooLocker interface {
	Foo()
	Lock()
	Unlock()
}

// Comma-ok assert: gc answers true (Lock/Unlock are in *sync.Mutex's
// method set, mutex.go pointer receivers).
func assertOkMutex() int {
	var m sync.Mutex
	var i any = &m
	if _, ok := i.(locker); ok {
		return 21
	}
	return 0
}

// Type switch: gc takes the locker branch.
func typeSwitchMutex() int {
	var m sync.Mutex
	var i any = &m
	switch i.(type) {
	case locker:
		return 12
	default:
		return 0
	}
}

// Bare assert: gc completes (no panic) — the model must not fabricate
// an "interface conversion ... missing method Lock" panic.
func bareAssertMutex() int {
	var m sync.Mutex
	var i any = &m
	l := i.(locker)
	_ = l
	return 1
}

// The definite-NO control: *sync.Mutex has no Foo, gc answers false.
func assertNegativeMissing() int {
	var m sync.Mutex
	var i any = &m
	if _, ok := i.(fooLocker); ok {
		return 99
	}
	return 2
}

// The definite-NO bare assert panics in gc, naming the first missing
// method: `interface conversion: *sync.Mutex is not main.fooLocker:
// missing method Foo`.
func bareAssertMissingPanics() int {
	var m sync.Mutex
	var i any = &m
	l := i.(fooLocker)
	_ = l
	return 0
}

// The other three primitives' method sets answer too (waitgroup.go /
// once.go pointer receivers).
func assertOkWaitGroup() int {
	var wg sync.WaitGroup
	var i any = &wg
	if _, ok := i.(interface {
		Add(int)
		Done()
		Wait()
	}); ok {
		return 31
	}
	return 0
}

func assertOkOnce() int {
	var o sync.Once
	var i any = &o
	if _, ok := i.(interface{ Do(func()) }); ok {
		return 41
	}
	return 0
}

// TryLock is out of scope as a CALL (sync/out-of-scope-trylock); its
// presence in the method set is still gc's answer to satisfaction.
func tryLockSigSatisfies() int {
	var m sync.Mutex
	var i any = &m
	if _, ok := i.(interface{ TryLock() bool }); ok {
		return 61
	}
	return 0
}

func main() {
	assertOkMutex()
}
