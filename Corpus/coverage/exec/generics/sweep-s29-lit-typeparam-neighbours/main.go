// Defect-neighbourhood campaign, shape S29 (synthetic-symbol bookkeeping; members
// BUG-031/027, and BUG-302 fixed in train 28), lane sweep/s28-s29-spelling-symbols,
// 2026-11-05 (docs/2026-10-27_defect-neighbourhood-campaign.md §4). BUG-302's
// neighbours: a func literal inside a generic function whose parameter or NAMED RESULT
// has a type that mentions a type parameter — `(r T)`, `[]T`, `*T`, `map[string]T`,
// `func(T) T`, a second type parameter `S`, a generic struct `gb[T]`, a nested literal's
// `T` parameter, and a generic TYPE's method — each at a concrete instantiation. Born on
// main 12d7a79a, where BUG-302 is open: every cell is the entry's B6 c4 whole-wire
// refusal (the stencil's substituted signature registers fresh parameter objects); with
// train 28's fix (lane frontend/fix-binding-1027) every cell agrees with gc, measured by
// this lane against the stage-29 frontend; expected = gc go1.26.5.

package main

type gb[T ~int] struct{ v T }

func (b gb[T]) withLit(v T) T {
	f := func(d T) T { return d + b.v }
	return f(v)
}

func gNamedRes[T ~int](v T) T {
	f := func() (r T) { r = v + 1; return }
	return f()
}

func gSliceParam[T ~int](v T) T {
	f := func(s []T) T { return s[0] }
	return f([]T{v})
}

func gPtrParam[T ~int](v T) T {
	f := func(p *T) T { return *p }
	return f(&v)
}

func gMapParam[T ~int](v T) T {
	f := func(m map[string]T) T { return m["k"] }
	return f(map[string]T{"k": v})
}

func gFuncParam[T ~int](v T) T {
	f := func(g func(T) T) T { return g(v) }
	return f(func(x T) T { return x * 2 })
}

func gSecondParam[T ~int, S ~string](v T, s S) int {
	f := func(d S) int { return len(d) }
	return int(v) + f(s)
}

func gStructParam[T ~int](v T) T {
	f := func(b gb[T]) T { return b.v }
	return f(gb[T]{v})
}

func gNestedParam[T ~int](v T) T {
	f := func() T {
		g := func(d T) T { return d }
		return g(v)
	}
	return f()
}

func litNamedResultT() int    { return int(gNamedRes(1)) }
func litSliceParamT() int     { return int(gSliceParam(2)) }
func litPtrParamT() int       { return int(gPtrParam(3)) }
func litMapParamT() int       { return int(gMapParam(4)) }
func litFuncParamT() int      { return int(gFuncParam(5)) }
func litSecondParamS() int    { return gSecondParam(6, "ab") }
func litStructParamT() int    { return int(gStructParam(7)) }
func litNestedParamT() int    { return int(gNestedParam(8)) }
func litInGenericMethodT() int { return gb[int]{9}.withLit(1) }

func main() {
	println("litNamedResultT", litNamedResultT())
	println("litSliceParamT", litSliceParamT())
	println("litPtrParamT", litPtrParamT())
	println("litMapParamT", litMapParamT())
	println("litFuncParamT", litFuncParamT())
	println("litSecondParamS", litSecondParamS())
	println("litStructParamT", litStructParamT())
	println("litNestedParamT", litNestedParamT())
	println("litInGenericMethodT", litInGenericMethodT())
}
