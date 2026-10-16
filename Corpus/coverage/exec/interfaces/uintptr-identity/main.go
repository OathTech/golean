// BUG-124 / FR-38 — `uintptr`'s runtime type IDENTITY (release-readiness
// punch list item 26; [USER] Mike 2026-10-12, D6: both halves agreed — refuse
// now, repair soon). spec#Numeric_types makes `uintptr` a distinct type. Before
// 2026-10-12 the decoder realized it as `uint64` (GoLean/NativeToIR.lean
// intKindOfName), so the two types were ONE identity at runtime and the six
// identity-bearing subjects below answered WRONGLY with status ok: gc
// go1.26.5 prints `false false 1 2 false false`, the machine printed
// `true true 64 1 true true` (the release-trust review's R1 probes,
// docs/2026-10-12_release-trust-review.md). The REFUSE half (lane
// fix/uintptr-refuse-1012) made each a by-name frontend refusal the same
// day; the REPAIR half (lane core/uintptr-repair-impl-1012; its shape [USER]
// Mike 2026-10-12, items 1 and 3-6 approved, item 4 = docs/2026-10-12_uintptr-repair-
// design.md D1–D5) gives the machine a DISTINCT `IntKind.uintptr` of width
// `intBits`, so every subject PASSes with gc's values through `Ty.eqb`'s
// structural equality and the guard is retired. Born at the repair:
// `uintptrMethodParam` / `uintptrMethodResult` (the method-set identity
// site: `M(uintptr)` is not `M(uint64)`), `uintptrArrayAssert` (`[1]uintptr`
// is not `[1]uint64`), `uintptrWrap` (width unchanged: 64 bits, unsigned),
// `uintptrAssertPanic` (the non-comma-ok assertion's panic text names the
// kind). The PASS controls, unchanged from the refuse lane: `widthOnly` —
// arithmetic, a conversion to uint64 and back, a pointer to uintptr passed
// to a non-interface parameter, a []uintptr and a map[uintptr] — width-only
// uses, correct at 64 bits (latitude inventory R1 / §11 item 6);
// `genericWidthOnly` — width-only generic code instantiated at uintptr, user
// stencils and source-through stdlib generics; `definedNominalU/S/E` and
// `genericNominal` — NAMED types over uintptr are nominal on the machine
// (the wire's `defined` def, the decoder's `.defined idx`): they box,
// assert, compare and switch exactly as in gc.
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

// S and S2 are two named structs of the same shape: nominal, distinct.
type S struct{ p uintptr }

type S2 struct{ p uintptr }

// definedNominalS: a boxed S asserts to S and NOT to the same-shaped S2 (the
// nominal-vs-structural witness, last round NIT-1: an unnamed `struct{p
// uint64}` target is frontier-refused, so S2 is the available one), compares
// equal to an equal S and unequal to a different one; a boxed *S asserts to
// *S. gc: 1+10+100+1000+10000 = 11111.
func definedNominalS() int {
	n := 0
	var x any = S{p: 3}
	if v, ok := x.(S); ok && v.p == 3 {
		n += 1
	}
	if _, ok := x.(S2); !ok {
		n += 10000
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

// G is a method-less generic struct: each instantiation is its own nominal
// type on the machine (distinct TypeIds), so the refusal does not scan type
// ARGUMENTS (last round LOW-1); a collapse through a method mentioning T
// is the method-set scan's business (B above, whose Get() T is in the set).
type G[T any] struct{ v T }

// genericNominal: a boxed G[uintptr] is not a G[uint64] (assertion,
// equality, type switch) and is a G[uintptr]. gc: 1+10+100+1000+10000 = 11111.
func genericNominal() int {
	n := 0
	var x any = G[uintptr]{v: 1}
	if _, ok := x.(G[uint64]); !ok {
		n += 1
	}
	if g, ok := x.(G[uintptr]); ok && g.v == 1 {
		n += 10
	}
	if x == any(G[uintptr]{v: 1}) {
		n += 100
	}
	if x != any(G[uint64]{v: 1}) {
		n += 1000
	}
	switch x.(type) {
	case G[uint64]:
		n += 50000
	case G[uintptr]:
		n += 10000
	}
	return n
}

// --- born at the repair 2026-10-12 (ported from 5f185fb3's ints/uintptr-identity; assert-panic new) ---

// PointerMethod's method set mentions uintptr in a PARAMETER: it satisfies
// PointerRequirement and NOT UintMethod (spec#Method_sets, spec#Type_identity:
// M(uintptr) and M(uint64) are different signatures).
type PointerMethod struct{}

func (PointerMethod) M(x uintptr) {}

type UintMethod interface{ M(uint64) }

type PointerRequirement interface{ M(uintptr) }

// uintptrMethodParam: the method-set identity site (satisfiesMethodSig
// compares the parameter lists). gc: 8.
func uintptrMethodParam() int {
	out := 0
	var v any = PointerMethod{}
	if _, ok := v.(UintMethod); ok {
		out += 1
	}
	if _, ok := v.(PointerRequirement); ok {
		out += 8
	}
	return out
}

// PointerResult's method set mentions uintptr in a RESULT.
type PointerResult struct{}

func (PointerResult) M() uintptr { return 7 }

type UintResult interface{ M() uint64 }

// uintptrMethodResult: M() uintptr does not satisfy M() uint64. gc: false.
func uintptrMethodResult() bool {
	var v any = PointerResult{}
	_, ok := v.(UintResult)
	return ok
}

// uintptrArrayAssert: the element's identity through an ARRAY type —
// [1]uintptr is not [1]uint64 and is [1]uintptr. gc: 2.
func uintptrArrayAssert() int {
	out := 0
	var a any = [1]uintptr{7}
	if _, ok := a.([1]uint64); ok {
		out += 1
	}
	if v, ok := a.([1]uintptr); ok && v[0] == 7 {
		out += 2
	}
	return out
}

// uintptrWrap: the width is unchanged by the identity — 64 bits, unsigned
// (^uintptr(0)+1 wraps to 0, the top bit is set, the round trip through
// uint64 is the identity). gc: true.
func uintptrWrap() bool {
	x := ^uintptr(0)
	return x+1 == 0 && x>>63 == 1 && uintptr(uint64(x)) == x
}

// uintptrAssertPanic: the non-comma-ok assertion panics with the kind's
// NAME in the text — gc `interface conversion: interface {} is uintptr, not
// uint64` (the collapsed machine would have returned 1 with status ok).
func uintptrAssertPanic() uint64 {
	var x any = uintptr(1)
	return x.(uint64)
}

func main() {
	println(uintptrAssert(), uintptrEqual(), uintptrSwitch(), uintptrMapKey(),
		uintptrSliceAssert(), uintptrPointerAssert(), widthOnly(),
		genericWidthOnly(), definedNominalU(), definedNominalS(), definedNominalE(),
		genericNominal(), uintptrMethodParam(), uintptrMethodResult(),
		uintptrArrayAssert(), uintptrWrap())
}
