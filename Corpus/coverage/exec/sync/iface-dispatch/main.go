package main

import "sync"

// PERMANENT-until-lifted refusal markers (arc-end fix round,
// 2026-08-10): a sync method call DISPATCHED THROUGH AN INTERFACE —
// user-defined or sync.Locker itself. Before the fix these escaped the
// F4 quarantine (which keys on the resolved selection's receiver; a
// dispatch through `main.locker` resolves to the interface, not
// sync.Mutex) and landed as runtime `stuck: dynamic type *sync.Mutex
// has no method Lock` — a misclassified red one layer too late. With
// the sync method-set stubs on the wire the boxing and the
// satisfaction ANSWER correctly, and the call itself refuses per-STUB
// with the precise frontend-quarantined reason (red at frontend-export
// by design). Lifting the calls — real stub bodies over the machine's
// existing sync ops — is the recorded follow-up (design note §12).

type locker interface {
	Lock()
	Unlock()
}

type waiter interface {
	Wait()
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
// (gc: 9). Before the fix this refused at the TYPE (emitType); it now
// boxes and answers satisfaction like any interface, and the call
// refuses at the stub.
func lockerBoxDispatch() int {
	var m sync.Mutex
	var l sync.Locker = &m
	l.Lock()
	x := 9
	l.Unlock()
	return x
}

func main() {
	mutexUserIface()
}
