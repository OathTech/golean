package main

// E2FLD (Stage E, family E2): `q.f += mut()` through a pointer, mut REDIRECTING the
// captured q from a to b — the frozen pointer VALUE is the field plan's anchor:
// {11100, 10101} (a.f*1000 + b.f). The frontend's OWN lowering only (the struct type's
// wire name is an envelope fact; the hand-built pointer and map witnesses cover the
// frozen-identity claim, this one the field-addr plan shape).
type P struct{ f int }

func e2fld() int {
	a, b := &P{f: 10}, &P{f: 100}
	q := a
	mut := func() int { q = b; return 1 }
	q.f += mut()
	return a.f*1000 + b.f
}

func main() { println(e2fld()) }
