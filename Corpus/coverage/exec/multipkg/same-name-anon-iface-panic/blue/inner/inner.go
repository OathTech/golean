package inner

// blue/inner: same package NAME as the other inner, distinct import PATH
// (BUG-097 / FR-19 panic-text pins, lane fr19-bug097 2026-09-05; the
// unexported-method shape lives in multipkg/unexported-method-scope — its
// whole-export guard would otherwise refuse this case too).
type T int

func (t T) Get() T { return t }

// W also has Get() T — a second concrete type behind Src's interface.
type W int

func (W) Get() T { return 0 }

func Make(v int) interface{ Get() T } { return T(v) }
func Src() interface{ Get() T }       { return T(7) }
func Assert(x any)                    { _ = x.(interface{ Get() T }) }
func AssertGet(x any)                 { _ = x.(interface{ get() int }) }
func IsGet(x any) bool                { _, ok := x.(interface{ get() int }); return ok }
