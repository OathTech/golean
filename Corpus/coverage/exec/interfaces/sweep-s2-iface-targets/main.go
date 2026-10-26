package main

// Defect-neighbourhood campaign, shape S2 (conversions: a missing kernel arm or a
// value not retagged), lane sweep/s2-conversions, 2026-10-26: every row is an
// agreement with gc on a route no earlier row held (the matrix is on the member
// entries' Neighbourhood lines in docs/BUGS.md; the plan is
// docs/2026-10-27_defect-neighbourhood-campaign.md §4).
// Interface targets: interface-to-interface conversions keep the dynamic type
// (the emitter passes the operand through), a DEFINED interface type as the
// target is the to-interface wrap (the kernel's interfaceDecl arm is unreachable
// from a type-checked wire), and a nil interface converted stays nil.

type I interface{ M() int }
type MyI interface{ M() int }
type J interface {
	I
	N() int
}
type T struct{ n int }

func (t T) M() int { return t.n }
func (t T) N() int { return t.n * 2 }

func ifaceToIface() int {
	var j J = T{3}
	i := I(j)
	a := any(j)
	e := I(any(T{4}).(I))
	k := 0
	if t, ok := a.(T); ok {
		k = t.n
	}
	if _, ok := i.(J); ok {
		k += 100
	}
	return i.M()*10 + k + e.M()*1000
}

func definedIfaceTarget() int {
	t := T{5}
	m := MyI(t)
	var i I = m
	var a any = MyI(i)
	r := 0
	switch a.(type) {
	case T:
		r = 1
	}
	return m.M()*100 + i.M()*10 + r
}

func nilIfaceToIface() (bool, bool, bool) {
	var j J
	i := I(j)
	a := any(i)
	var e error
	return i == nil, a == nil, any(e) == nil
}

func main() {}
