package inner

// blue/inner: same package NAME as red/inner, distinct import PATH.
type T int

func (t T) Get() T { return t }

// Make returns an ANONYMOUS interface value whose method signature
// mentions this package's T — spelled `interface{ Get() inner.T }` under
// a package-NAME qualifier, exactly like red/inner's.
func Make(v int) interface{ Get() T } { return T(v) }

// Is asks whether x carries THIS package's `interface{ Get() T }`.
func Is(x any) bool { _, ok := x.(interface{ Get() T }); return ok }
