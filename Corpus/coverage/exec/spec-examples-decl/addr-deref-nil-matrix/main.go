package main

// BUG-056 probe matrix (bug-fix arc slice 3, 2026-08-19; landed BEFORE any
// fix, colors recorded pre-fix in docs/bugfix-arc-log.md §slice 3).
//
// spec#Address_operators: "If the evaluation of x would cause a run-time
// panic, then the evaluation of &x does too" — and for pointer indirection,
// "If x is nil, an attempt to evaluate *x will cause a run-time panic."
// Every nil subject below panics under gc go1.26.5 with the runtime.Error
// "invalid memory address or nil pointer dereference"
// (artifacts/probe/addr056, scratch — expectations computed from `go run`
// BEFORE the differential ran).
//
// The matrix walks the COMPOSITIONS around the bare `&*p` collapse that the
// two existing pins (address-op-nil-indirection/addr-deref-nil{,-paren})
// leave uncovered: double indirection with the nil at either level, the
// collapse UNDER an enclosing index/field address (where the enclosing
// node's own nil check makes the collapse benign — pinned green so the fix
// cannot regress them), the auto-deref sugar forms the BUG entry recorded
// without witnesses, the non-nil aliasing identity the collapse gets right
// (and the fix must keep), and `&*` in argument / call-operand positions.

type Point struct{ x, y int }

// addrTwoDerefOuterNil: `&**pp` with pp == nil. The OPERAND of the outer
// indirection is `*pp`, a genuine load of a nil pointer — the panic comes
// from evaluating the operand, before the &* composition is even reached.
func addrTwoDerefOuterNil() int {
	var pp **int
	q := &**pp
	_ = q
	return 0
}

// addrTwoDerefInnerNil: `&**pp` with pp valid and *pp == nil. The inner
// load succeeds and yields nil; the outer `&*` must then nil-check it.
// This is the double-indirection form of the BUG-056 collapse: the wire
// keeps the inner deref (a real load) and drops the outer nil check.
func addrTwoDerefInnerNil() int {
	var p *int
	pp := &p
	q := &**pp
	_ = q
	return 0
}

// addrIndexSlicePtrNil: `&(*sp)[0]` with sp == nil. The collapse cannot
// fire (the * is not immediately under &); the deref of sp is a real load
// and panics on nil.
func addrIndexSlicePtrNil() int {
	var sp *[]int
	q := &(*sp)[0]
	_ = q
	return 0
}

// addrIndexArrPtrNil: `&(*ap)[0]` with ap == nil, pointer-to-ARRAY base.
// Here the &-of-* collapse DOES fire inside the index-addr operand (an
// array base takes its address), but the enclosing index-addr nil-checks
// its base itself (BUG-038's check) — the collapse is benign under this
// composition. Pinned green so the fix cannot disturb it.
func addrIndexArrPtrNil() int {
	var ap *[4]int
	q := &(*ap)[0]
	_ = q
	return 0
}

// addrIndexAutoDeref: `&ap[0]` with ap == nil — the auto-deref sugar for
// the previous subject (spec: a[x] on a pointer to array is shorthand for
// (*a)[x]). The BUG entry recorded `&p[i]`-on-nil as panicking correctly
// but record-only; this is its witness.
func addrIndexAutoDeref() int {
	var ap *[4]int
	q := &ap[0]
	_ = q
	return 0
}

// addrFieldExplicit: `&(*st).x` with st == nil — the explicit form of the
// field address through a nil pointer. The wire emits a real field-addr
// node whose base is the pointer VALUE; the machine nil-checks it there.
func addrFieldExplicit() int {
	var st *Point
	q := &(*st).x
	_ = q
	return 0
}

// addrFieldAutoDeref: `&st.x` with st == nil — the auto-deref sugar form.
// The BUG entry recorded `&p.f`-on-nil as panicking correctly but
// record-only; this is its witness.
func addrFieldAutoDeref() int {
	var st *Point
	q := &st.x
	_ = q
	return 0
}

// addrDerefAlias: the NON-NIL identity the collapse gets right and any fix
// must preserve — `&*p` is p itself (the same variable, not a copy): a
// store through the derived pointer is visible through the original cell.
func addrDerefAlias() int {
	x := 7
	p := &x
	q := &*p
	*q = 42
	return x
}

// addrDerefArg: `&*p` on nil in ARGUMENT position — the composition must
// panic during argument evaluation, before the callee runs.
func addrDerefArg() int {
	var p *int
	sink(&*p)
	return 0
}

//go:noinline
func sink(q *int) { _ = q }

// addrDerefCall: `&*retNil()` — the &* operand is a call result, not a
// variable. The call completes; the &* of its nil result must panic.
func addrDerefCall() int {
	q := &*retNil()
	_ = q
	return 0
}

func retNil() *int { return nil }

func main() {
	println(addrDerefAlias())
}
