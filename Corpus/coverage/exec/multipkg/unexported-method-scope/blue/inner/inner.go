package inner

// blue/inner: same package NAME as the other inner, distinct import PATH
// (BUG-098 / FR-29 pins, lane fr19-bug097 2026-09-05): an UNEXPORTED
// method name is package-scoped — this package's `get` is
// `blue/inner.get`, and only its own `interface{ get() int }` requires it.
type T int

func (t T) get() int { return int(t) }

func Make(v int) any   { return T(v) }
func AssertGet(x any)  { _ = x.(interface{ get() int }) }
func IsGet(x any) bool { _, ok := x.(interface{ get() int }); return ok }
