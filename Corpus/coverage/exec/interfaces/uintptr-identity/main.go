// BUG-124 / FR-38 — `uintptr`'s runtime type IDENTITY (lane
// fix/uintptr-refuse-1012, 2026-10-12; release-readiness punch list item 26,
// [USER] Mike 2026-10-12 «D6: agree on both - refuse and repair asap.» — the
// REFUSE half). The decoder realizes `uintptr` as `uint64`
// (GoLean/NativeToIR.lean intKindOfName), so the two types are ONE identity
// at runtime and every identity-bearing use answered WRONGLY with status ok
// before the refusal: gc go1.26.5 prints `false false 1 2 false false` for
// the six subjects below (spec#Numeric_types: uintptr is a distinct type),
// the machine printed `true true 64 1 true true` (the release-trust
// review's R1 probes, docs/2026-10-12_release-trust-review.md — its
// reproduction block, re-run at the lane base 4365c313, is the red-first).
// Since the lane, each of the six REFUSES BY NAME at the frontend
// (tools/nativefrontend/uintptrid.go) at its boxing or target position —
// FAIL/frontend-export RED BY DESIGN on BUG-124's Cases line (Expect: FAIL),
// retired by the parked `typed-uintptr-identity` repair when it lands. The
// PASS controls: `widthOnly` — arithmetic, a conversion to uint64 and back,
// a pointer to uintptr passed to a non-interface parameter, a []uintptr and
// a map[uintptr] — width-only uses, correct at 64 bits (latitude inventory
// §11 item 6) and never boxed; `genericWidthOnly` (fix round MEDIUM-1) —
// width-only generic code instantiated at uintptr, user stencils and
// source-through stdlib generics; `definedNominalU/S/E` (fix round LOW-1) —
// NAMED concrete types over uintptr are nominal on the machine (the wire's
// `defined` def, the decoder's `.defined idx`): they box, assert, compare
// and switch exactly as in gc, so the refusal does not enter a named
// type's underlying structure (its METHOD SET only).
package main

import "slices"

// uintptrAssert: comma-ok assertion of a boxed uintptr to uint64 — gc false.
func uintptrAssert() bool {
	var x any = uintptr(1)
	_, ok := x.(uint64)
	return ok
}

// uintptrEqual: interface equality across the two types — gc false.
func uintptrEqual() bool {
	return any(uintptr(1)) == any(uint64(1))
}

// uintptrSwitch: a type switch over a boxed uintptr — gc takes `case
// uintptr` (1); the collapsed machine took `case uint64` (64).
func uintptrSwitch() int {
	var x any = uintptr(1)
	switch x.(type) {
	case uint64:
		return 64
	case uintptr:
		return 1
	}
	return 0
}

// uintptrMapKey: two distinct dynamic types are two keys — gc 2.
func uintptrMapKey() int {
	return len(map[any]int{uintptr(1): 7, uint64(1): 9})
}

// uintptrSliceAssert: the element type's identity through a slice — gc false.
func uintptrSliceAssert() bool {
	var x any = []uintptr{1}
	_, ok := x.([]uint64)
	return ok
}

// uintptrPointerAssert: the pointee's identity through a pointer — gc false.
func uintptrPointerAssert() bool {
	n := uintptr(1)
	var x any = &n
	_, ok := x.(*uint64)
	return ok
}

//go:noinline
func bump(p *uintptr) {
	*p += 2
}

// widthOnly: the PASS control — no uintptr-mentioning value is ever boxed
// into an interface and no assertion names one.
func widthOnly() int {
	var p uintptr = 40
	bump(&p)
	q := uint64(p) * 3
	s := []uintptr{p, uintptr(q)}
	m := map[uintptr]int{s[0]: 1, s[1]: 2}
	return int(q) + int(p) + m[s[1]]*len(s)
}

// --- fix round 2026-10-12: the trimmed rule's PASS controls ---

// U is a defined type over uintptr: NOMINAL on the machine (BUG-124's rule
// enters a named type's method set only, never its underlying).
type U uintptr

func id[T any](x T) T { return x }

func maxOf[T ~uintptr | ~uint64](a, b T) T {
	if a > b {
		return a
	}
	return b
}

type B[T any] struct{ v T }

func (b B[T]) Get() T { return b.v }

// genericWidthOnly: user stencils at uintptr (a function, a constrained
// function, a method stencil, a defined type over uintptr) and the
// source-through stdlib generics slices.Max / slices.Clone — the template's
// result tuple is substituted in the scan (MEDIUM-1). gc: 7+9+5+7+9+3 = 40.
func genericWidthOnly() int {
	p := id(uintptr(7))
	q := maxOf(uintptr(3), uintptr(9))
	r := B[uintptr]{v: 5}.Get()
	s := id(U(7))
	xs := []uintptr{1, 9, 3}
	c := slices.Clone(xs)
	return int(p) + int(q) + int(r) + int(s) + int(slices.Max(xs)) + len(c)
}

// definedNominalU: a boxed U is not a uint64 (assertion, equality, type
// switch), a boxed *U is not a *uint64 but is a *U. gc: 1+100+1000+10000+100000 = 111101.
func definedNominalU() int {
	n := 0
	var x any = U(1)
	if _, ok := x.(uint64); !ok {
		n += 1
	}
	if x != any(uint64(1)) {
		n += 100
	}
	switch x.(type) {
	case uint64:
		n += 5000
	case U:
		n += 1000
	}
	u := U(2)
	var y any = &u
	if _, ok := y.(*uint64); !ok {
		n += 10000
	}
	if _, ok := y.(*U); ok {
		n += 100000
	}
	return n
}

// S is a named struct with a uintptr field: nominal.
type S struct{ p uintptr }

// definedNominalS: a boxed S asserts to S, compares equal to an equal S and
// unequal to a different one; a boxed *S asserts to *S. gc: 1+10+100+1000 = 1111.
func definedNominalS() int {
	n := 0
	var x any = S{p: 3}
	if v, ok := x.(S); ok && v.p == 3 {
		n += 1
	}
	if x == any(S{p: 3}) {
		n += 10
	}
	if x != any(S{p: 4}) {
		n += 100
	}
	var y any = &S{p: 1}
	if _, ok := y.(*S); ok {
		n += 1000
	}
	return n
}

// E (over uintptr) and F (over uint64) are two error types, distinct by name.
type E uintptr

func (E) Error() string { return "e" }

type F uint64

func (F) Error() string { return "f" }

// definedNominalE: an E in an error is not an F, is an E, and differs from
// an F in another error. gc: 1+10+100+1000 = 1111.
func definedNominalE() int {
	n := 0
	var err error = E(1)
	if _, ok := err.(F); !ok {
		n += 1
	}
	if e, ok := err.(E); ok && e == 1 {
		n += 10
	}
	if err.Error() == "e" {
		n += 100
	}
	var err2 error = F(1)
	if err != err2 {
		n += 1000
	}
	return n
}

func main() {
	println(uintptrAssert(), uintptrEqual(), uintptrSwitch(), uintptrMapKey(),
		uintptrSliceAssert(), uintptrPointerAssert(), widthOnly(),
		genericWidthOnly(), definedNominalU(), definedNominalS(), definedNominalE())
}
