// BUG-123 / FR-38 — `uintptr`'s runtime type IDENTITY (lane
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
// FAIL/frontend-export RED BY DESIGN on BUG-123's Cases line (Expect: FAIL),
// retired by the parked `typed-uintptr-identity` repair when it lands. The
// seventh subject, `widthOnly`, is the PASS control: arithmetic, a
// conversion to uint64 and back, a pointer to uintptr passed to a
// non-interface parameter, a []uintptr and a map[uintptr] — width-only
// uses, correct at 64 bits (latitude inventory §11 item 6) and never boxed.
package main

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

func main() {
	println(uintptrAssert(), uintptrEqual(), uintptrSwitch(), uintptrMapKey(),
		uintptrSliceAssert(), uintptrPointerAssert(), widthOnly())
}
