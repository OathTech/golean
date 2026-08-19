package main

// BUG-063 guardrails (bug-fix arc audit fix round, 2026-08-19; landed
// BEFORE the fix, colors recorded pre-fix in docs/bugfix-arc-log.md).
//
// The IMPLICIT address-of in receiver position. spec#Calls: for a
// pointer-receiver method m of &x's method set, "x.m() is shorthand
// for (&x).m()" when x is addressable — and when x is itself an
// indirection `*q`, that implicit `&x` is the `&*q` composition, which
// spec#Address_operators gives its own eager panic clause ("if the
// evaluation of x would cause a run-time panic, then the evaluation of
// &x does too", exhibit `&*x  // causes a run-time panic`). gc probes q
// for nil at receiver evaluation (artifacts/probe/a1-recv, scratch —
// every expectation below computed from `go run` at go1.26.5 BEFORE the
// differential ran: 100, 100, 7808, 100).
//
// The machine's explicit-`&*` arm (BUG-056, emitUnaryExpr) already
// lowers to the addr-of-deref strict op — but the RECEIVER-position
// implicit `&` routes through emitAddressOf's general StarExpr arm,
// which collapses &*q to q unchecked. For nil q the panic is silently
// lost on the METHOD paths: the method runs with a nil receiver.
// (The sync-primitive path collapses too, but its consumer nil-checks
// the operand itself — see syncRecvNil below, pinned GREEN.)
//
// Every subject observes through recover so the RECOVERABILITY of the
// panic (a runtime.Error) and the execution order around it are both
// pinned, not just the status.

import "sync"

type recvT struct{ x int }

// M never touches its receiver: the panic, if any, must come from the
// implicit &*q at receiver evaluation, never from a body deref.
func (t *recvT) M() int { return 5 }

// inc mutates through the receiver — the aliasing witness for the
// non-nil control (the bound receiver must be q itself, not a copy).
func (t *recvT) inc() int { t.x++; return t.x }

// explicitCallNil: `(*q).M()` with q == nil. gc panics at the implicit
// &(*q) (recovered -> 100); the pre-fix machine collapses the address
// and calls M on the nil receiver (-> 5).
func explicitCallNil() int {
	var q *recvT
	r := 0
	func() {
		defer func() {
			if recover() != nil {
				r = 100
			}
		}()
		r = (*q).M()
	}()
	return r
}

// methodValueNil: `f := (*q).M` with q == nil — the receiver is
// captured AT METHOD-VALUE TIME (spec#Method_values), so gc panics at
// the BINDING, before r += 10 runs (-> 100). A fix that panicked at the
// CALL instead would score 110; the pre-fix machine binds and calls
// (-> 115).
func methodValueNil() int {
	var q *recvT
	r := 0
	func() {
		defer func() {
			if recover() != nil {
				r += 100
			}
		}()
		f := (*q).M
		r += 10
		r += f()
	}()
	return r
}

// nonNilControl: the same two shapes on a VALID q — pinned green so the
// fix cannot tax the non-nil path, and the receiver identity is
// observed (inc's mutations land in t through both the direct call and
// the bound method value): a=7, b=8, t.x=8 -> 7808.
func nonNilControl() int {
	t := recvT{x: 6}
	q := &t
	a := (*q).inc()
	f := (*q).inc
	b := f()
	return a*1000 + b*100 + t.x
}

// syncRecvNil: the sync-primitive receiver takes its own emission path
// (syncRecvAddr) with the same StarExpr collapse — but here the
// collapse is BENIGN: the machine's lock op nil-checks its own operand
// (valueAsLoc), so machine and gc both panic-and-recover to 100. Pinned
// GREEN pre-fix as the control that the unified receiver routing must
// not disturb (the index-arr-ptr-nil precedent: a consumer's own nil
// check covers the composition). NOTE (probed, artifacts/probe/
// a1-recv/sync2.go): the panic's order against ARGUMENT calls —
// `(*wp).Add(bump())` — is unsequenced latitude (the I-2/E-family UNSEQ
// reading; the receiver probe is not a call, so left-to-right does not
// order it), and gc realizes args-first (1007). A strict row on that
// shape would pin one conforming member against another, so none is
// added.
func syncRecvNil() int {
	var mp *sync.Mutex
	r := 0
	func() {
		defer func() {
			if recover() != nil {
				r = 100
			}
		}()
		(*mp).Lock()
		r = 1
	}()
	return r
}

func main() {
	println(explicitCallNil())
	println(methodValueNil())
	println(nonNilControl())
	println(syncRecvNil())
}
