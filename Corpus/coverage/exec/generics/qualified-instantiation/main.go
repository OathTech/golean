package main

// FR-27 (2026-09-04, lane fr27-fr28): EXPLICIT instantiation of a
// package-QUALIFIED source generic function — `gset.Immutable[string](…)`
// — in callee and value position. cedar-go's `mapset.Immutable[EntityUID]
// (args...)` (types/entity_uid.go:143; the census §11 witnesses
// NewEntityUIDSet / doInEval / types.go:117) refused with the shape-blind
// text `generic instantiation <pos>`: emit.go's IndexExpr/IndexListExpr
// arms handed the base to genericFuncValue, which resolved an identifier
// base only, while the INFERRED spelling `gset.Immutable(args...)`
// lowered through emitQualifiedCall. The fix resolves a qualified
// SelectorExpr base to the same `funcInstanceAt(sel.Sel, fn)` the
// inferred path uses (genericFuncUse), so both spellings share one
// stencil. `gset` is a case-local source package (the corpus multi-
// package convention, docs/2026-08-18_multipackage-identity.md).
//
// Rows: call (callee position, plus the inferred twin in the same
// subject), func-value (value position), nested (a qualified generic
// TYPE as the type argument; IndexListExpr with two arguments; a
// qualified explicit instantiation as a func-typed ARGUMENT), method-
// value / method-expr (a method of the instantiated qualified type as a
// value / as a method expression), source-through (the same shape into a
// SOURCE-THROUGH stdlib package: `slices.Index[[]int, int]` — the real
// generic stencils), stdlib-refused (RED frontend-export BY DESIGN: the
// shape into a stdlib package the register does NOT admit as source-
// through — `maps.Clone[map[string]int]` — refuses BY NAME on FR-14's
// `stdlib-qualified selector … in value position` text, never the
// shape-blind fallback).

import (
	"gset"
	"maps"
	"slices"
)

func b2i(b bool) int {
	if b {
		return 1
	}
	return 0
}

// call: explicit qualified instantiation in CALLEE position, beside its
// inferred twin (one stencil for both spellings).
func qualCall() int {
	explicit := gset.Immutable[string]("a", "b", "a")
	inferred := gset.Immutable("c", "d", "e", "c")
	return explicit.Len()*10 + inferred.Len() // 23
}

// func-value: explicit qualified instantiation in VALUE position.
func qualFuncValue() int {
	mk := gset.Immutable[string]
	sum := gset.Sum[int]
	return mk("x", "y").Len()*100 + sum([]int{1, 2, 3}) // 206
}

// nested: a qualified generic TYPE as the type argument, the two-
// argument IndexListExpr spelling, and a qualified explicit
// instantiation passed as a func-typed argument.
func qualNested() int {
	boxed := gset.Wrap[gset.Box[int]](gset.Wrap[int](7))
	applied := gset.Apply[int, gset.Box[int]](gset.Wrap[int], 3)
	return boxed.V.V*10 + applied.V // 73
}

// method-value: a method of the instantiated qualified type as a value.
func qualMethodValue() int {
	s := gset.Make[int](1, 2, 3)
	has := s.Contains
	return b2i(has(2))*10 + b2i(has(9)) + s.Len()*100 // 310
}

// method-expr: a method EXPRESSION over the instantiated qualified type.
func qualMethodExpr() int {
	lenOf := gset.Set[int].Len
	return lenOf(gset.Make[int](4, 5, 6, 4)) // 3
}

// source-through: the same shape into a stdlib package the register
// admits as source-through — the real generic stencils.
func qualSourceThrough() int {
	idx := slices.Index[[]int, int]([]int{5, 6, 7}, 6)
	return idx*10 + b2i(slices.Contains[[]int, int]([]int{5, 6, 7}, 7)) // 11
}

// stdlib-refused (RED BY DESIGN, frontend-export): the shape into a
// stdlib package that is NOT source-through refuses BY NAME (FR-14's
// `stdlib-qualified selector maps.Clone in value position …`). NOT
// called from main: the frontend quarantines the declaration.
func qualStdlibRefused() int {
	m := map[string]int{"a": 1, "b": 2}
	c := maps.Clone[map[string]int](m)
	return len(c)
}

func main() {
	qualCall()
	qualFuncValue()
	qualNested()
	qualMethodValue()
	qualMethodExpr()
	qualSourceThrough()
}
