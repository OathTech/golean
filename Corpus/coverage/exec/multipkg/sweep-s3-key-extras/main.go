// Sweep lane sweep/s3-type-keys (2026-10-26), shape S3 «type identity keys: fusion or
// spurious distinction» of the defect-neighbourhood campaign
// (docs/2026-10-27_defect-neighbourhood-campaign.md §4; the matrix and the probe ids are on the
// `- Neighbourhood:` lines of BUG-124/098/100/097/092/067/010/018 in docs/BUGS.md). Every row
// is strict, expected = gc go1.26.5; each subject is one cell (type kind × route) of the matrix,
// born green: the machine agreed with gc on every one at the lane base 89ba27c5.
package main

// Extra cells read off the key-minting code: an anonymous interface embedding another
// package's PRIVATE named interface flattens to that package's unexported method (one type
// with its own literal); a LOCAL named interface is nominal; an anonymous literal embedding a
// local named interface flattens; method-expression and method-value types; variadic and
// result arity inside interface method signatures; instantiations inside interface keys; a
// package-level type shadowed by a local inside a generic; a stencil's local at byte vs
// uint8 / alias / any spellings; a package-level `error` and `T` beside the universe error
// and a type parameter T.

import (
	bi "blue/inner"
	ri "red/inner"
)

type Box[T any] struct{ v T }
type A = int
type S struct{}
type T struct{ Tag int }

// An anonymous literal embedding red/inner.Private IS red/inner's own `interface{ get() int }`.
func extraEmbeddedPrivate() int {
	s := 0
	var x any = ri.FnGet()
	if _, ok := x.(func(interface{ ri.Private })); ok {
		s += 1
	}
	if _, ok := x.(func(ri.Private)); ok {
		s += 10
	}
	if _, ok := x.(func(interface{ get() int })); ok {
		s += 100
	}
	if _, ok := any(ri.T{}).(interface{ ri.Private }); ok {
		s += 1000
	}
	if _, ok := any(ri.T{}).(interface{ get() int }); ok {
		s += 10000
	}
	return s // 1001
}

func mkIA() (any, func(any) int) {
	type I interface{ M() }
	return func(I) {}, func(x any) int {
		r := 0
		if _, ok := x.(func(I)); ok {
			r += 1
		}
		if _, ok := x.(func(interface{ M() })); ok {
			r += 10
		}
		if _, ok := x.(func(interface{ I })); ok {
			r += 100
		}
		return r
	}
}

func mkIB() (any, func(any) int) {
	type I interface{ M() }
	return func(I) {}, func(x any) int {
		r := 0
		if _, ok := x.(func(I)); ok {
			r += 1
		}
		return r
	}
}

// Local named interfaces are nominal; a literal embedding one flattens to the literal.
func extraLocalIface() int {
	fa, isA := mkIA()
	fb, isB := mkIB()
	var lit any = func(interface{ M() }) {}
	return isA(fa)*10000 + isA(fb)*1000 + isB(fb)*100 + isA(lit)*1 // 10110
}

// Method expressions and method values: func(ri.T) string ≢ func(bi.T) string; a method
// value is a plain func() string.
func extraMethodExprTypes() int {
	s := 0
	if _, ok := any(ri.T.Name).(func(bi.T) string); ok {
		s += 1
	}
	if _, ok := any(ri.T.Name).(func(ri.T) string); ok {
		s += 10
	}
	if _, ok := any(ri.T{}.Name).(func() string); ok {
		s += 100
	}
	// (*ri.T).Name — a method expression over a value-receiver method — is a named frontend
	// refusal of another shape (S5: "deref adapter not modeled"), left out of this cell.
	if _, ok := any(ri.T.Name).(func(T) string); ok {
		s += 10000
	}
	return s // 10110
}

// Variadic, result arity and instantiations inside interface method signatures.
func extraIfaceSigs() int {
	s := 0
	var v any = func(interface{ M(...int) }) {}
	if _, ok := v.(func(interface{ M([]int) })); ok {
		s += 1
	}
	if _, ok := v.(func(interface{ M(...int) })); ok {
		s += 10
	}
	var r any = func(interface{ M() int }) {}
	if _, ok := r.(func(interface{ M() (int, error) })); ok {
		s += 100
	}
	if _, ok := r.(func(interface{ M() (n int) })); ok {
		s += 1000
	}
	var g any = func(interface{ Get() Box[int] }) {}
	if _, ok := g.(func(interface{ Get() Box[int64] })); ok {
		s += 10000
	}
	if _, ok := g.(func(interface{ Get() Box[A] })); ok {
		s += 100000
	}
	return s // 101010
}

func shadowS[T any](x T) any {
	type S struct{ v T }
	return S{x}
}

// A package-level S shadowed by a stencil's local S.
func extraShadowInGeneric() int {
	s := 0
	if _, ok := shadowS(1).(S); ok {
		s += 1
	}
	if shadowS(1) == any(S{}) {
		s += 10
	}
	if shadowS(1) == shadowS(2) {
		s += 100
	}
	if shadowS(1) == shadowS(1) {
		s += 1000
	}
	return s // 1000
}

func extraReadoutShadow() any { return shadowS(1) } // Name() S[int]

func wrap[T any](x T) any {
	type box struct{ v T }
	return box{x}
}

// A stencil's local at fused argument spellings.
func extraStencilFused() int {
	s := 0
	if wrap[byte](1) == wrap[uint8](1) {
		s += 1
	}
	if wrap[A](1) == wrap[int](1) {
		s += 10
	}
	if wrap[any](nil) == wrap[interface{}](nil) {
		s += 100
	}
	if wrap[int](1) == wrap[int64](1) {
		s += 1000
	}
	if wrap[T](T{1}) == wrap[T](T{1}) {
		s += 10000
	}
	return s // 10111
}

func extraReadoutStencilNamedArg() any { return wrap[T](T{1}) }  // Name() box[main.T]
func extraReadoutStencilByte() any     { return wrap[byte](1) }  // Name() box[uint8]

func mkTP[T any](x T) any { return Box[T]{x} }

// A type parameter named like the package-level T.
func extraTypeParamShadow() int {
	s := 0
	if mkTP(1) == any(Box[int]{1}) {
		s += 1
	}
	if _, ok := mkTP(1).(Box[T]); ok {
		s += 10
	}
	if _, ok := mkTP(T{}).(Box[T]); ok {
		s += 100
	}
	return s // 101
}

func main() {}
