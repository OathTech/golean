package inner

// Shared source of `red/inner` and `blue/inner` (same package NAME,
// distinct import PATHS). P has no methods; Q has a VALUE-receiver method;
// R has a POINTER-receiver method — the three shapes gc's pkgpath() of
// `*T` distinguishes (reflectdata: a pointer type has a package path iff
// its method set is non-empty, and then it is T's package).

type P struct{ V int }

type Q struct{ V int }

func (q Q) M() int { return q.V }

type R struct{ V int }

func (r *R) M() int { return r.V }

func MkP() any { return &P{1} }
func MkQ() any { return &Q{1} }
func MkR() any { return &R{1} }

func MkSliceQ() any { return []Q{{1}} }
