// BUG-059's POINTER shapes (audit fix round R1 of lane fr19-bug097,
// 2026-09-05 — the first cut answered `""` for the pkgpath of EVERY
// non-TypeId type, so `*inner.Q, not *inner.Q` carried ` (types from
// different scopes)` where gc prints ` (types from different packages)`).
// gc's rule (`runtime/type.go` rtype.pkgpath, `reflectdata/reflect.go`
// uncommonSize/typePkg @ go1.26.5, probed): a type has a package path
// exactly when it has an uncommon section — a named type, or an unnamed
// type with a NON-EMPTY method set — and `*T`'s package is `T`'s. So:
//
//	*P (no methods)          → "" vs ""            → (types from different scopes)
//	*Q (value-receiver M)    → red/inner vs blue/inner → (types from different packages)
//	*R (pointer-receiver M)  → red/inner vs blue/inner → (types from different packages)
//	[]Q (unnamed slice)      → "" vs ""            → (types from different scopes)
//
// The machine derives the pointer's answer from the wire's method table
// and, when no method is on the wire, from the method-set record (`full`
// ⇒ empty; `exported`/absent ⇒ REFUSE by name) — never a guess.
package main

import (
	bi "blue/inner"
	ri "red/inner"
)

// gc: interface conversion: interface {} is *inner.P, not *inner.P (types from different scopes)
func pointerNoMethods() int {
	x := ri.MkP()
	p := x.(*bi.P)
	return p.V
}

// gc: interface conversion: interface {} is *inner.Q, not *inner.Q (types from different packages)
func pointerValueMethod() int {
	x := ri.MkQ()
	q := x.(*bi.Q)
	return q.M()
}

// gc: interface conversion: interface {} is *inner.R, not *inner.R (types from different packages)
func pointerPointerMethod() int {
	x := ri.MkR()
	r := x.(*bi.R)
	return r.M()
}

// gc: interface conversion: interface {} is []inner.Q, not []inner.Q (types from different scopes)
func sliceOfMethodType() int {
	x := ri.MkSliceQ()
	s := x.([]bi.Q)
	return len(s)
}

func main() {}
