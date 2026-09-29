package main

import "sync"

// Born pins for the G-P audit's F1 (docs/2026-09-29_method-promotion-audit.md;
// fix round 2026-09-29, lane core/method-promotion-0928): interface DISPATCH
// to a promoted DECLARATION-ONLY STUB entry — here a promoted sync-primitive
// method (sync.Mutex.Lock promoted through an embedded *sync.Mutex).
//
// Before G-P S2 the stub was an ordinary non-wrapper Func, so a NIL *S box
// fell into BUG-087's panicwrap family: the machine admitted TWO panic texts
// {nil-deref, "value method main.psPtrEmbed.Lock called using nil *psPtrEmbed
// pointer"} through the nilValueMethodText pick. gc's wrappee is the embedded
// *sync.Mutex, not psPtrEmbed, so gc's panicwrap test (types.Identical(
// wrapper.Elem(), wrappee)) fails: gc dereferences and gives the nil-deref
// text only. Since G-P S2 the stub is a promotion RECORD, outside the family,
// and the machine admits the nil-deref text only (the nil-first check the
// retired stub's entry made).
//
// With a NON-nil box the dispatch refuses by name on both sides (the stub's
// cause); the retired stub entry also read the whole pointee before refusing,
// the record does not — the psBoxSyncStubRace subject is that read's only
// observable (gc -race reports the race on p.Mutex).

type psLocker interface{ Lock() }

type psPtrEmbed struct {
	*sync.Mutex
	z int
}

// The audit's shape: the concrete type is visible (gc devirtualizes the
// call to the (*psPtrEmbed).Lock wrapper; the text is the same either way).
func psNilBoxSyncStub() int {
	var p *psPtrEmbed
	var l psLocker = p
	l.Lock()
	return 0
}

//go:noinline
func psLockVia(l psLocker) { l.Lock() }

// The itab shape: an opaque callee dispatches through the itab entry.
func psNilBoxSyncStubItab() int {
	var p *psPtrEmbed
	psLockVia(p)
	return 0
}

// A non-nil box: gc locks the embedded mutex and returns 1; the machine
// refuses the dispatch by name (the stub record's cause).
func psBoxSyncStub() int {
	p := &psPtrEmbed{Mutex: &sync.Mutex{}}
	var l psLocker = p
	l.Lock()
	return 1
}

// A non-nil box beside a concurrent write of the embedded pointer field:
// gc's wrapper reads p.Mutex unsynchronized with the child's write — a race
// under -race. The machine refuses the dispatch by name on every schedule.
func psBoxSyncStubRace() int {
	p := &psPtrEmbed{Mutex: &sync.Mutex{}}
	var l psLocker = p
	done := make(chan int)
	go func() {
		p.Mutex = &sync.Mutex{}
		done <- 1
	}()
	l.Lock()
	return <-done
}

func main() {}
