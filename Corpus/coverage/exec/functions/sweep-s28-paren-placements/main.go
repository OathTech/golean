// Defect-neighbourhood campaign, shape S28 (spelling admission; members BUG-136/115, and
// BUG-287 fixed in train 26), lane sweep/s28-s29-spelling-symbols, 2026-11-05
// (docs/2026-10-27_defect-neighbourhood-campaign.md §4). The parenthesised spellings at
// the other placements: inside a func literal, inside a generic function at two
// instantiations, in a method body on its receiver, in package-level initializers and
// init(), and beside calls on the unseq path; expected = gc go1.26.5.

package main

type pt struct{ f int }

func (p *pt) paren() int {
	(p).f = 1
	(*p).f++
	(p.f) += 10
	((*p).f)++
	return p.f // 13
}

func one() int { return 1 }

var gx = (1) + (2)
var gp = (*pt)(nil)
var gs = [](int){(1), (2)}
var gy (int) = (one)()
var gm = map[(string)](int){("k"): (4)}

func init() {
	(gx) += 10
	(gs[0]) = 5
	(gm["k"])++
}

type myI int

func parenInClosure() int {
	x := 0
	s := []int{0}
	p := &pt{}
	f := func() {
		(x) = (x) + 5
		(s[0])++
		(p.f) += 2
		(p).f++
	}
	f()
	f()
	g := func(k (int)) (int) { return (k) * 2 }
	return x*1000 + s[0]*100 + p.f*10 + g(3) // 10266
}

func parenInGeneric[T ~int](v T) T {
	x := v
	(x) = (x) + 1
	s := [](T){x, (T)(2)}
	var y (T) = (T)((len)((s)))
	z := (int)(x)
	if (nil) == (any)(nil) {
		y++
	}
	return x*100 + y*10 + T(z)
}

func parenInGenericBoth() int {
	return int(parenInGeneric(1)) + int(parenInGeneric(myI(2)))*10000 // 232 + 3330000
}

func parenInMethod() int {
	p := &pt{}
	return p.paren()
}

func parenPackageLevel() int {
	n := gx*100000 + gs[0]*10000 + gs[1]*1000 + gy*100 + gm["k"]*10
	if gp == nil {
		n++
	}
	return n // 1352511
}

var cnt int

func bump() int { cnt++; return cnt }

func parenBesideCalls() int {
	cnt = 0
	x, y := 0, 0
	s := []int{0, 0}
	m := map[int]int{}
	a, b := 0, 0
	(x), y = 1, bump()
	(s[0]), m[1] = bump(), bump()
	(a), (b) = bump(), bump()
	return x + y*10 + s[0]*100 + m[1]*1000 + a*10000 + b*100000 // 1+10+200+3000+40000+500000 = 543211
}

func main() {
	println("parenInClosure", parenInClosure())
	println("parenInGenericBoth", parenInGenericBoth())
	println("parenInMethod", parenInMethod())
	println("parenPackageLevel", parenPackageLevel())
	println("parenBesideCalls", parenBesideCalls())
}
