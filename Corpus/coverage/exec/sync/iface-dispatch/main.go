package main

import "sync"

// LIFTED (Q-SYNCVAL slice, P-S2-6, 2026-09-01; rows were
// PERMANENT-until-lifted refusal markers from the arc-end fix round
// 2026-08-10): a sync method call DISPATCHED THROUGH AN INTERFACE —
// user-defined or sync.Locker itself — now EXECUTES: dispatch lands on
// the bodied sync method stub, whose body is the same `sync-op` the
// direct call lowers to (one syncOpFor table), so the dispatched op
// consumes the same machine op / same C8 acquisition site as the
// direct form. THE IDENTITY PRINCIPLE ([USER]-RULED 2026-08-31):
// indirection preserves op identity or refuses — never a variant.
// History: before the 2026-08-10 stubs these escaped the F4 quarantine
// and landed as runtime `stuck`; the stubs made satisfaction/boxing
// answer while calls refused per-stub; this slice gave the modeled
// ops real bodies. Unmodeled members (TryLock, RLocker, ...) still
// refuse per-stub at dispatch.

type locker interface {
	Lock()
	Unlock()
}

type waiter interface {
	Wait()
}

type doer interface {
	Do(func())
}

// Dispatch through a user-defined Lock/Unlock interface (gc: 42).
func mutexUserIface() int {
	var m sync.Mutex
	var l locker = &m
	l.Lock()
	x := 42
	l.Unlock()
	return x
}

// Dispatch through a user-defined Wait interface (gc: 8; the zero
// counter makes Wait return immediately).
func wgUserIface() int {
	var wg sync.WaitGroup
	var w waiter = &wg
	w.Wait()
	return 8
}

// sync.Locker itself — the stdlib's name for the same capability
// (gc: 9). Boxing and satisfaction answered since the 2026-08-10
// stubs; the call executes since the Q-SYNCVAL lift.
func lockerBoxDispatch() int {
	var m sync.Mutex
	var l sync.Locker = &m
	l.Lock()
	x := 9
	l.Unlock()
	return x
}

// RWMutex WRITE ops through sync.Locker (gc: 11): the dispatched
// Lock/Unlock on a *sync.RWMutex resolve to wlock/wunlock — the same
// ops the direct calls lower to, per the identity principle.
func rwLockerDispatch() int {
	var rw sync.RWMutex
	var l sync.Locker = &rw
	l.Lock()
	x := 11
	l.Unlock()
	return x
}

// Once.Do through a user interface (gc: 1): both dispatched calls
// consume the SAME once cell — f runs exactly once (the bodied stub is
// the generic Do: onceBegin, deferred completion in the stub's own
// frame, then f).
func onceIfaceDispatch() int {
	var o sync.Once
	var d doer = &o
	n := 0
	d.Do(func() { n++ })
	d.Do(func() { n++ })
	return n
}

// MISUSE IDENTITY: a dispatched second Lock on the same mutex parks
// the only goroutine into gc's deadlock fatal exactly like the direct
// form (sync/mutex-double-lock) — pins that dispatch consumed the SAME
// acquisition op, not a variant that absorbs the second Lock.
func lockerDoubleLock() int {
	var m sync.Mutex
	var l sync.Locker = &m
	l.Lock()
	l.Lock()
	return 0
}

func main() {
	mutexUserIface()
}
