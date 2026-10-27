package main

// Sweep lane sweep/s10-panics (2026-10-27), shape S10: the type-assertion
// panic (spec#Type_assertions) at two raising shapes the interfaces/* rows do
// not pin — an assertion to a TYPE PARAMETER inside a generic body, and a nil
// `error` asserted to a concrete pointer type. The text is S12's; the kind
// (a run-time panic of the TypeAssertionError class) is probed here.

type akErr struct{ code int }

func (e *akErr) Error() string { return "ak" }

func akAs[T any](x any) T { return x.(T) }

func assertTypeParam() int {
	return akAs[int](any("s"))
}

func nilErrorAssert() int {
	var e error
	p := e.(*akErr)
	return p.code
}

func main() {}
