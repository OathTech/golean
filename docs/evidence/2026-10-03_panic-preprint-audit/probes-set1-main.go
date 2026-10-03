package main

// AUDIT PROBES for the preprint phase (pre-merge audit of lane
// core/panic-preprint-1003, 2026-10-03; [AGENT] auditor, branch
// review/panic-preprint-1003). Scratch rows beyond the lane's 21: gc at the
// pin (go1.26.5) is the oracle; the machine's answer is compared through
// the ordinary differential harness. NOT a corpus contribution — the file
// lives only on the audit branch's evidence.

// ---- shared payload types: CALLED:<s> on stderr is the observed call count ----

type ev struct{ s string }

func (e ev) Error() string {
	println("CALLED:" + e.s)
	return e.s
}

type ep struct{ s string }

func (e *ep) Error() string {
	println("CALLED:" + e.s)
	return e.s
}

// A1 an interface value holding a value with Error()
func ifaceHoldingError() {
	var err error = ev{"x"}
	panic(err)
}

// A2 Error() promoted through an embedded INTERFACE field (the `.iface`
// dispatch anchor of preprintTargetFid)
type wrap struct{ error }

func embeddedIfacePromoted() { panic(wrap{ev{"inner"}}) }

// A3 the embedded interface is nil: the promoted call dereferences nil
// inside the wrapper -> gc's fatal names runtime.errorString (BUG-099:
// the machine refuses by name)
func embeddedIfaceNil() { panic(wrap{}) }

// A4 a defined STRING type with Error()
type dstr string

func (s dstr) Error() string { return string(s) + "!" }

func definedStringType() { panic(dstr("hi")) }

// A5 a defined SLICE type
type dslice []int

func (l dslice) Error() string { return "len2" }

func definedSliceType() { panic(dslice{1, 2}) }

// A6 a defined MAP type
type dmap map[string]int

func (dmap) Error() string { return "m" }

func definedMapType() { panic(dmap{}) }

// A7 a defined FUNC type (nil func value in the box)
type dfunc func()

func (dfunc) Error() string { return "f" }

func definedFuncType() { panic(dfunc(nil)) }

// A8 a defined BOOL type with String()
type dbool bool

func (dbool) String() string { return "b" }

func definedBoolStringer() { panic(dbool(true)) }

// A9 a defined FLOAT type
type dfloat float64

func (dfloat) Error() string { return "fl" }

func definedFloatType() { panic(dfloat(1.5)) }

// A10 a defined ARRAY type
type darr [2]int

func (darr) Error() string { return "arr" }

func definedArrayType() { panic(darr{1, 2}) }

// A11 pointer receiver; the pointee is mutated by a deferred call before
// the method runs (post-defer state through the pointer)
func ptrMutatedByDefer() {
	e := &ep{"a"}
	defer func() { e.s = "b" }()
	panic(e)
}

// A12 a named result modified by the method's own deferred call
type namedRes int

func (namedRes) Error() (s string) {
	defer func() { s = "changed" }()
	return "orig"
}

func namedResultDefer() { panic(namedRes(1)) }

// A13 the method recovers ITS OWN panic and sets the named result
type selfRecover int

func (selfRecover) Error() (s string) {
	defer func() {
		if recover() != nil {
			s = "recovered-inner"
		}
	}()
	panic("inner")
}

func methodRecoversOwnPanic() { panic(selfRecover(1)) }

// A15 newer entry a string, older an error (only the older is called)
func newerStringOlderError() {
	defer func() {
		recover()
		panic("str")
	}()
	panic(ev{"err"})
}

// A16 older entry a string, newer an error
func olderStringNewerError() {
	defer func() {
		recover()
		panic(ev{"err"})
	}()
	panic("str")
}

// A17 call ORDER observed through state: the newest's method sets a
// global the oldest's method returns
var shared = "unset"

type setter int

func (setter) Error() string {
	shared = "set-by-newest"
	return "setter"
}

type getter int

func (getter) Error() string { return shared }

func stateOrderAcrossMethods() {
	defer func() {
		recover()
		panic(setter(1))
	}()
	panic(getter(1))
}

// A18 THREE entries, the same box each time (two adjacent collisions)
func threeSameBox() {
	e := &ep{"same"}
	defer func() {
		recover()
		panic(e)
	}()
	defer func() {
		recover()
		panic(e)
	}()
	panic(e)
}

// A19 distinct TYPES with equal fields: never identical in gc
type ev2 struct{ s string }

func (e ev2) Error() string {
	println("CALLED2:" + e.s)
	return e.s
}

func distinctTypesEqualFields() {
	defer func() {
		recover()
		panic(ev2{"x"})
	}()
	panic(ev{"x"})
}

// A20 distinct POINTERS to equal pointees: never identical
func distinctPointersEqualPointee() {
	defer func() {
		recover()
		panic(&ep{"x"})
	}()
	panic(&ep{"x"})
}

// A21 the recovered box re-panicked: a struct with a SLICE field (not
// comparable under Go ==; gc compares eface words)
type withSlice struct{ xs []int }

func (withSlice) Error() string {
	println("CALLED:ws")
	return "ws"
}

func sameBoxSliceField() {
	defer func() {
		r := recover()
		panic(r)
	}()
	panic(withSlice{[]int{1}})
}

// A22 a MAP payload re-panicked through recover (pointer-shaped box)
type dmapc map[string]int

func (dmapc) Error() string {
	println("CALLED:m")
	return "m"
}

func mapPayloadRepanic() {
	m := dmapc{}
	defer func() {
		r := recover()
		panic(r)
	}()
	panic(m)
}

// A23 equal entries that are NOT adjacent: no collapse anywhere
func nonAdjacentEqual() {
	e := &ep{"x"}
	defer func() {
		recover()
		panic(e)
	}()
	defer func() {
		recover()
		panic(&ep{"y"})
	}()
	panic(e)
}

// A24 String() with a pointer receiver on a pointer payload
type sp struct{}

func (*sp) String() string { return "sp" }

func stringerPtrReceiver() { panic(&sp{}) }

// A25 the value has String() only; the pointer has Error() too
type mix int

func (mix) String() string  { return "S" }
func (*mix) Error() string { return "E" }

func mixValue() { panic(mix(1)) }

func mixPointer() {
	m := mix(1)
	panic(&m)
}

// A26 the method spawns a goroutine and completes a channel round trip
// (the world is still running: probe p15)
type spawner int

func (spawner) Error() string {
	ch := make(chan string)
	go func() { ch <- "from-goroutine" }()
	return <-ch
}

func methodSpawnsGoroutine() { panic(spawner(1)) }

// A27 a NON-MAIN goroutine panics with an error payload while main blocks
func goroutinePanicsError() {
	go func() { panic(ev{"from-g"}) }()
	<-make(chan int)
}

// A28 a non-main goroutine re-panics the same box: the phase's collision
// draw under the POOL (poolThreadOblivious must refuse; the enumerator
// carries the row)
func goroutineRepanicSameBox() {
	go func() {
		defer func() {
			r := recover()
			panic(r)
		}()
		panic(&ep{"g"})
	}()
	<-make(chan int)
}

// A29 the method panics with a POINTER-typed payload: gc prints
// `type *main.inner2`; the machine refuses (unpinned family)
type inner2 struct{ x int }

type panicsPtr int

func (panicsPtr) Error() string { panic(&inner2{1}) }

func methodPanicsPtr() { panic(panicsPtr(1)) }

// A30 the method panics with an int: gc `type int`; the machine refuses
type panicsInt int

func (panicsInt) Error() string { panic(42) }

func methodPanicsInt() { panic(panicsInt(1)) }

// A31 the method panics with an ERROR-typed payload: gc names the type and
// never calls ITS Error() (no CALLED:inner on stderr)
type panicsErr int

func (panicsErr) Error() string { panic(ev{"inner"}) }

func methodPanicsErrorTyped() { panic(panicsErr(1)) }

// A32 the method panics with a defined STRING type: `type main.dstr2`
type dstr2 string

type panicsDStr int

func (panicsDStr) Error() string { panic(dstr2("x")) }

func methodPanicsDefinedString() { panic(panicsDStr(1)) }

// A33 the method panics with nil: gc `type *runtime.PanicNilError`; the
// machine's twin refuses by name
type panicsNil int

func (panicsNil) Error() string { panic(nil) }

func methodPanicsNil() { panic(panicsNil(1)) }

// A34 the method panics with a multi-line string: the fatal's first line
type panicsMulti int

func (panicsMulti) Error() string { panic("l1\nl2") }

func methodPanicsMultiline() { panic(panicsMulti(1)) }

// A35 the method's DEFERRED call panics after a normal return
type deferPanics int

func (deferPanics) Error() string {
	defer func() { panic("in-defer") }()
	return "x"
}

func methodDeferPanics() { panic(deferPanics(1)) }

// A36 recover() called DIRECTLY in the method body (not deferred): nil
type directRecover int

func (directRecover) Error() string {
	if recover() == nil {
		return "nil-recover"
	}
	return "non-nil"
}

func methodRecoverDirect() { panic(directRecover(1)) }

// A42 an interface type embedding error, holding a value with both methods
type codeErr interface {
	error
	Code() int
}

type ce struct{}

func (ce) Error() string { return "ce" }
func (ce) Code() int     { return 1 }

func ifaceEmbeddingError() {
	var m codeErr = ce{}
	panic(m)
}

// A44 a VALUE receiver reached through a non-nil pointer payload (auto-deref)
type v2 int

func (v2) Error() string { return "v2" }

func valueReceiverOnPtr() {
	v := v2(1)
	panic(&v)
}

// A45 promoted through a nil embedded *T with a POINTER receiver and a
// constant body: fine in gc
type inPtr struct{}

func (*inPtr) Error() string { return "in" }

type outPtr struct{ *inPtr }

func embeddedNilPtrConst() { panic(outPtr{}) }

// A45b promoted through a nil embedded *T with a VALUE receiver: gc's
// wrapper throws (panicwrap -> runtime.plainError; refused by name)
type inVal struct{}

func (inVal) Error() string { return "inv" }

type outVal struct{ *inVal }

func embeddedNilPtrValueRecv() { panic(outVal{}) }

// A46 an UNRECOVERED chain: head a string, then an identical pair
func headStringNewerPair() {
	e := &ep{"e"}
	defer func() { panic(e) }()
	defer func() { panic(e) }()
	panic("s")
}

// A47 the ABORT's own head draw after the phase settled the newest entry
// (recovered "s" head, equal "s" successor, pending error newest)
func headDrawAfterPhase() {
	defer func() {
		recover()
		panic(ev{"e"})
	}()
	defer func() {
		recover()
		panic("s")
	}()
	panic("s")
}

// A49 Error() wins over String() with pointer receivers too
type bothPtr struct{}

func (*bothPtr) Error() string  { return "E" }
func (*bothPtr) String() string { return "S" }

func errorWinsPtr() { panic(&bothPtr{}) }

// A50 the NEWEST entry's method mutates the OLDEST entry's pointee before
// the oldest is called (newest-first order with state)
var oldest = &ep{"o"}

type mutator int

func (mutator) Error() string {
	oldest.s = "mutated"
	return "mut"
}

func newestMutatesOldest() {
	defer func() {
		recover()
		panic(mutator(1))
	}()
	panic(oldest)
}

// A51 equal payloads built at RUN time (no static dedup in gc)
func repanicRuntimeEqual() {
	b := []byte("rt")
	defer func() {
		recover()
		panic(ev{string(b)})
	}()
	panic(ev{string(b)})
}

// A53 a goroutine's method blocks while main is blocked: every goroutine
// asleep -> the bare deadlock line
type blocker2 int

func (blocker2) Error() string {
	<-make(chan int)
	return "never"
}

func goroutineMethodBlocksDeadlock() {
	go func() { panic(blocker2(1)) }()
	<-make(chan int)
}

// A54 main's method blocks and is WOKEN by another goroutine
var wake = make(chan int)

type waiter int

func (waiter) Error() string {
	<-wake
	return "woken"
}

func methodWokenByGoroutine() {
	go func() { wake <- 1 }()
	panic(waiter(1))
}

// A55 the method recovers its own panic and returns the zero string: gc
// prints `panic: ` with an EMPTY payload line (observed via a sentinel
// line printed first so the row has a non-empty expectation to miss)
type emptyAfterRecover int

func (emptyAfterRecover) Error() string {
	defer func() { recover() }()
	panic("inner")
}

func methodReturnsEmpty() { panic(emptyAfterRecover(1)) }

// A56 a recovered error entry followed by a Goexit-free second panic of a
// different error TYPE whose Error reads the first's recovered flag? (no:
// not observable) -- instead: a chain of three DISTINCT error payloads,
// every method called, newest first
func threeDistinct() {
	defer func() {
		recover()
		panic(ev{"c"})
	}()
	defer func() {
		recover()
		panic(ev{"b"})
	}()
	panic(ev{"a"})
}

// A57 the recovered box re-panicked where the payload is a defined INT
// with a pointer-receiver Error (pointer payload): `*dint` box identity
type dint int

func (d *dint) Error() string {
	println("CALLED:dint")
	return "dint"
}

func repanicPtrToInt() {
	d := dint(3)
	defer func() {
		r := recover()
		panic(r)
	}()
	panic(&d)
}

// A58 a value payload whose method set has Error through a pointer only is
// NOT rewritten even when a recovered copy exists (method-set rule holds
// across the chain)
type ponly struct{ n int }

func (*ponly) Error() string { return "p" }

func valueNotInSetTwice() {
	defer func() {
		recover()
		panic(ponly{2})
	}()
	panic(ponly{1})
}
