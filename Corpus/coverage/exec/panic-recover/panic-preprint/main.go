package main

// THE PREPRINT PHASE (BUG-004 item 4, window unit 6b; design note
// docs/2026-09-30_bug004-item4-design.md §2 (i), RULED [USER] Mike
// 2026-09-30 — «Yes, agree, do the fix inside this window», relayed by the
// [AGENT] coordinator; lane core/panic-preprint-1003). gc's `preprintpanics`
// (runtime/panic.go:702–730 at the pin, go1.26.5) CALLS a panic payload's
// `Error()` / `String()` on the panicking goroutine — after every deferred
// call, before anything prints, with the world still running — and prints
// the returned string like any string payload. The machine runs the same
// calls as ordinary machine steps at the empty continuation (Machine.lean
// `Cont.preprintK`, the `preprint*` rules). Every row below is one of the
// design note's gc probes (docs/evidence/2026-09-30_bug004-item4-design/
// probes.md, cited pNN), red-first on main (the abort line of an
// `error`/`Stringer` payload was the standing fail-closed refusal).

// ---- p01: `error` wins over `fmt.Stringer` (panic.go:722–725's order) ----

type both int

func (both) Error() string  { return "from-Error" }
func (both) String() string { return "from-String" }

func errorWinsOverStringer() { panic(both(1)) }

// ---- p02/p03: a panic INSIDE the method is gc's unrecoverable fatal
// `panic while printing panic value: …` — exit 2, the original `panic:`
// line never printed. A string payload prints its text; a defined-type
// payload prints `type <gc type string>`. ----

type panicsString int

func (panicsString) Error() string { panic("inner-string") }

func methodPanicsString() { panic(panicsString(1)) }

type panicsDefined int

type inner struct{ x int }

func (panicsDefined) Error() string { panic(inner{7}) }

func methodPanicsDefined() { panic(panicsDefined(1)) }

// ---- p04: a nil *T receiver dereferenced inside Error() — the fatal names
// gc's CONCRETE runtime-error type (`runtime.errorString`), which the
// machine's one `runtime.Error` twin cannot (BUG-099): REFUSED by name,
// a red-by-design pin on BUG-099's Cases line. ----

type ptrMsg struct{ msg string }

func (e *ptrMsg) Error() string { return e.msg }

func nilPtrReceiverDeref() {
	var e *ptrMsg
	panic(e)
}

// ---- p05: a constant-returning method on a nil *T receiver is fine. ----

type ptrConst struct{ msg string }

func (e *ptrConst) Error() string { return "const-text" }

func nilPtrReceiverConst() {
	var e *ptrConst
	panic(e)
}

// ---- p06: a VALUE method through a nil *T — gc's `panicwrap` throws before
// the body runs: `type runtime.plainError` (BUG-099, refused by name). ----

type valueMethod int

func (valueMethod) Error() string { return "v-text" }

func valueMethodNilPtr() {
	var p *valueMethod
	panic(p)
}

// ---- p07: a pointer-receiver method is NOT in the value's method set —
// the value payload prints `printanycustomtype`'s `main.T(v)` (the chain's
// second entry prints an address on line two, unobserved). ----

type ptrOnly int

func (*ptrOnly) Error() string { return "q" }

type ptrOnlyStruct struct{ a int }

func (*ptrOnlyStruct) Error() string { return "p" }

func ptrMethodNotInValueSet() {
	defer func() { panic(ptrOnlyStruct{5}) }()
	panic(ptrOnly(3))
}

// ---- p08: the method runs AFTER every deferred call — it sees post-defer
// state. ----

var msgState = "before"

type postDefer int

func (postDefer) Error() string { return msgState }

func postDeferState() {
	defer func() { msgState = "after" }()
	panic(postDefer(1))
}

// ---- p09/p10: only UNRECOVERED payloads are called, newest first. ----

type named struct{ s string }

func (e named) Error() string {
	println("CALLED:" + e.s)
	return e.s
}

func recoveredNotCalled() {
	func() {
		defer func() { recover() }()
		panic(named{"recovered-one"})
	}()
	println("after-recover")
	panic(named{"unrecovered"})
}

func chainOrder() {
	defer func() {
		recover()
		panic(named{"second"})
	}()
	panic(named{"first"})
}

// ---- p11/p11b/p12/p21: gc's identity check (panic.go:715) at an EQUAL
// adjacent pair decides the CALL COUNT as well as the suffix — the
// `repanicCollapse` pick, drawn by the phase at the pair (bound 2): slot 0
// = identical eface (one call, the collapsed line), slot 1 = distinct (both
// called, the two-line form). Membership rows: both members admitted; gc's
// draw recorded per row. ----

type namedPtr struct{ s string }

func (e *namedPtr) Error() string {
	println("CALLED:" + e.s)
	return e.s
}

// The recovered box passed through: gc draws slot 0 (p11).
func repanicSameBox() {
	defer func() {
		r := recover()
		panic(r)
	}()
	panic(&namedPtr{"same"})
}

type smallInt int

func (c smallInt) Error() string {
	println("CALLED")
	return "boom"
}

// The value re-boxed by the assertion: gc draws slot 1 (p11b).
func repanicReboxed() {
	defer func() {
		r := recover()
		panic(r.(smallInt))
	}()
	panic(smallInt(9))
}

// Two equal literals: gc draws slot 0 (static dedup, p12).
func repanicDistinctEqual() {
	defer func() {
		recover()
		panic(named{"x"})
	}()
	panic(named{"x"})
}

// An UNRECOVERED identical pair: one call, `panic: same` with no suffix
// (gc draws slot 0, p21); slot 1 calls both.
func unrecoveredEqualPair() {
	e := &namedPtr{"same"}
	defer func() { panic(e) }()
	panic(e)
}

// ---- p13: `panic(nil)` is the `*runtime.PanicNilError` runtime error,
// already gc's rewritten text — the phase leaves it alone; the abort's
// own collapse pick applies. ----

func panicNilRepanic() {
	defer func() {
		r := recover()
		panic(r)
	}()
	panic(nil)
}

// ---- p14: a method that blocks with no other runnable goroutine —
// `checkdead`'s bare deadlock line, the pending panic never printed. ----

type blocker int

func (blocker) Error() string {
	<-make(chan int)
	return "never"
}

func blockingMethodDeadlock() { panic(blocker(9)) }

// ---- p17: the method's own `recover()` sees nothing (its frame is not a
// deferred frame of the panicking call). ----

type recoverer int

func (recoverer) Error() string {
	defer func() {
		r := recover()
		println("inner-recover-nil:", r == nil)
	}()
	return "text"
}

func recoverInsideMethod() { panic(recoverer(9)) }

// ---- p18: a wrong signature is not the runtime's interface — no rewrite. ----

type wrongStringer int

func (wrongStringer) String() int { return 1 }

type wrongError int

func (wrongError) Error(x int) string { return "no" }

func wrongSignatureNotRewritten() {
	defer func() { panic(wrongError(4)) }()
	panic(wrongStringer(3))
}

// ---- p19: a PROMOTED method counts (the method set is the carrier's). ----

type embeddedErr struct{}

func (embeddedErr) Error() string { return "promoted-text" }

type outer struct {
	embeddedErr
	n int
}

func promotedError() { panic(outer{n: 1}) }

// ---- p20: the rewritten text prints like a string payload — the first
// line stops at the first LF (`printindented`). ----

type multi int

func (multi) Error() string { return "line-one\nline-two" }

func multilineText() { panic(multi(1)) }

// ---- p24: another goroutine, blocked, does not deadlock the phase — the
// world is still running when the method is called. ----

var otherCh = make(chan int)

type gotText int

func (gotText) Error() string { return "got" }

func otherGoroutineBlocked() {
	go func() {
		for {
			<-otherCh
		}
	}()
	panic(gotText(1))
}
