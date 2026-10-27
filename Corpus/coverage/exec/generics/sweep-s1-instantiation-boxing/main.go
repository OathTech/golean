package main

// Defect-neighbourhood campaign, shape S1 (implicit conversion omitted at an
// assignable context), lane sweep/s1-implicit-conv, 2026-10-27: every row is an
// agreement with gc on a route no earlier row held (the matrix is on the member
// entries' Neighbourhood lines in docs/BUGS.md; the plan is
// docs/2026-10-27_defect-neighbourhood-campaign.md §4).
// GENERIC INSTANTIATIONS: whether a `T` slot boxes is a property of the
// instantiated type (the wrap substitutes the active instantiation first) —
// an explicit `[any]` argument boxes, `[int64]` makes the untyped constant
// take int64, inference gives the default type; a constraint-typed parameter
// returned as the constraint; a generic struct's `T` field at `any` and at a
// defined type; a generic method's `T` result; a variadic `...T` at `any`;
// `comparable` at `any` distinguishing the int and float64 boxes of `1` and
// `1.0`.

type tDef int

type tStr interface{ String() string }

type tS struct{}

func (tS) String() string { return "tS" }

func gid[T any](x T) T { return x }

func gToAny[T any](x T) any { return x }

func gBoxS[T tStr](x T) tStr { return x }

type gBox[T any] struct{ V T }

func (b gBox[T]) Get() T { return b.V }

func gFirst[T any](xs ...T) T { return xs[0] }

func gEq[T comparable](a, b T) bool { return a == b }

func explicitAnyArg() any { return gid[any](3) }

func constTakesTypeParam() (any, any) { return gToAny[int64](3), gToAny[float32](1) }

func inferredDefault() (any, any, any) { return gToAny(3), gToAny(2.5), gToAny('a') }

func constraintTyped() (string, string) { return gBoxS(tS{}).String(), gBoxS[tS](tS{}).String() }

func boxLitAny() (any, any) {
	b := gBox[any]{V: 3}
	return b.V, b.Get()
}

func boxLitDefined() any {
	b := gBox[tDef]{3}
	return b.Get()
}

func methodResultAny() any { return gBox[any]{V: "s"}.Get() }

func variadicAny() (any, any) { return gFirst[any](1, "a"), gFirst[any]("a", 1) }

func comparableAnyDefault() (bool, bool, bool) {
	return gEq[any](1, 1.0), gEq[any](1, 1), gEq[any]("a", "a")
}

func inferredIntReturned() any { return gid(3) }

func main() {
	explicitAnyArg()
}
