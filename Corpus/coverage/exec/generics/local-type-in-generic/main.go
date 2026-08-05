package main

// A type DECLARED INSIDE a generic function: gc names it with the
// enclosing instantiation's type arguments (reflect.Type.Name() gives
// "ltgBox[int]", String() "main.ltgBox[int]") — probe-verified on
// go1.26.5. The stencil path used to mint the bare TypeId "main.ltgBox"
// (no parameterization), so the observation channel reported the wrong
// dynamic name and the interface-conversion panic text named the wrong
// type. Arc-final audit F3 (2026-08-06), red-first.

func ltgWrap[T any](x T) any {
	type ltgBox struct{ v T }
	return ltgBox{x}
}

// Observation-bearing: the dynamic name of the boxed local type.
func localTypeDynamicName() any {
	return ltgWrap(3)
}

// Panic-text-bearing: a failed assert names the dynamic type.
func localTypeAssertPanic() int {
	a := ltgWrap(4)
	return a.(int)
}
