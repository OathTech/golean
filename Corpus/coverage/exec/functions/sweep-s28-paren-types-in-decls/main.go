// Defect-neighbourhood campaign, shape S28 (spelling admission; members BUG-136/115, and
// BUG-287 fixed in train 26), lane sweep/s28-s29-spelling-symbols, 2026-11-05
// (docs/2026-10-27_defect-neighbourhood-campaign.md §4). Parenthesised types in variable,
// type and function declarations (`var x (int)`, `type T (int)`, `func f(x (int)) (int)`),
// in struct fields and in method signatures; expected = gc go1.26.5.

package main

type pt struct{ a (int); b (string) }

type pInt (int)
type pStruct (struct{ v int })
type pSlice ([]int)
type pPtr (*pt)
type pFunc (func() int)
type pIface (interface{ val() int })

func (p pInt) val() int { return int(p) * 2 }

func (p (pt)) first() int { return p.a }

func (p (*pt)) second() string { return p.b }

func paramParen(x (int), ys ...(int)) (int) {
	n := x
	for _, y := range ys {
		n += y
	}
	return n
}

func resultParens() ((int)) { return 3 }

func namedResultParen() (r (int)) { r = 4; return }

func (p *pt) setA(v (int)) { p.a = v }

func parenVarDecls() int {
	var x (int)
	var y (int) = 5
	var p (*pt)
	var s ([]int)
	var f (func() int)
	var m (map[string]int)
	var c (chan int)
	var a ([2]int)
	var e (error)
	var i (any)
	var st (pt)
	var u, w (int) = 1, 2
	x = 1
	s = append(s, 1, 2)
	f = func() int { return 7 }
	m = map[string]int{"k": 1}
	c = make(chan int, 1)
	c <- 3
	a[1] = 9
	st.a = 6
	i = 8
	n := x + y*10 + len(s)*100 + f()*1000 + len(m)*10000 + <-c*100000 + a[1]*1000000 + st.a*10000000 + i.(int)*100000000
	if p == nil && e == nil {
		n += u + w
	}
	return n // 897317251+3
}

func parenTypeDecls() int {
	type local (int)
	type localS (struct{ q int })
	var l local = 3
	var ls localS
	ls.q = 4
	var pi pInt = 5
	var ps pStruct
	ps.v = 6
	sl := pSlice{7, 8}
	pp := pPtr(&pt{9, "z"})
	var pf pFunc = func() int { return 10 }
	var pif pIface = pi
	var st pt
	st.setA(11)
	st.b = "ab"
	n := int(l) + ls.q*10 + pi.val()*100 + ps.v*1000 + len(sl)*10000 + (*pt)(pp).first()*100000 + len((*pt)(pp).second())*0 + pf()*1000000 + pif.val()*10000000 + st.a*100000000 + len(st.b)*1000000000
	return n + paramParen(1, 2, 3) + resultParens() + namedResultParen() // ... gc decides
}

func main() {
	println("parenVarDecls", parenVarDecls())
	println("parenTypeDecls", parenTypeDecls())
}
