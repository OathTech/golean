// Defect-neighbourhood campaign, shape S28 (spelling admission; members BUG-136/115, and
// BUG-287 fixed in train 26), lane sweep/s28-s29-spelling-symbols, 2026-11-05
// (docs/2026-10-27_defect-neighbourhood-campaign.md §4). Parenthesised types in type
// assertions and type-switch cases, in explicit instantiations, inside generic bodies
// (`(T)(x)`, `var y (T)`, `[](T){}`), and parenthesised method expressions and values
// beyond the covered (T).M / (*T).M forms; expected = gc go1.26.5.

package main

type pt struct{ v int }

func (p pt) get() int   { return p.v }
func (p *pt) inc() int  { p.v++; return p.v }

type inner struct{ k int }

func (i inner) key() int { return i.k }

type wrap struct{ inner }

type getter interface{ get() int }

type box[T any] struct{ x T }

func (b box[T]) val() T { return b.x }

func ident[T any](x T) T { return x }

func conv[T ~int](x T) int {
	y := (int)(x)
	var z (T) = (T)(y + 1)
	s := [](T){z}
	var a any = (any)(s[0])
	return y + int(a.(T))*10
}

func parenAssertions() int {
	var x any = pt{3}
	var g getter = pt{4}
	p := x.((pt))
	q, ok := g.((pt))
	gp := x.((getter))
	n := p.v + q.v*10 + gp.get()*100
	if ok {
		n += 1000
	}
	switch x.(type) {
	case (int), ((string)):
		n += 10000
	case ((pt)):
		n += 100000
	}
	return n // 101343
}

func parenInstantiations() int {
	a := ident[(int)](5)
	b := box[(string)]{"ab"}
	c := box[([]int)]{[]int{1, 2, 3}}
	d := box[[]int]{[]int{4}}
	return a + len(b.val())*10 + len(c.val())*100 + len(d.x)*1000 + conv[(int)](7)*10000 + conv(myI(2))*1000000 // 5+20+300+1000+870000+32000000
}

type myI int

func parenMethodExprsValues() int {
	t := pt{1}
	p := &pt{10}
	w := wrap{inner{100}}
	b := box[int]{7}
	var g getter = pt{2}
	f1 := ((pt)).get
	f2 := ((*pt)).inc
	f4 := (wrap).key
	f5 := (getter).get
	f6 := (box[int]).val
	m1 := (t).get
	m2 := (&t).inc
	m3 := (*p).get
	m4 := (p).get
	m5 := (p).inc
	m6 := (w).key
	m7 := (w).inner.key
	m8 := (g).get
	return f1(t) + f2(p)*10 + f4(w)*1000 + f5(g)*10000 + f6(b)*100000 + m1() + m2()*10 + m3()*100 + m4()*1000 + m5()*10000 + m6()*100000 + m7()*1000000 + m8()*10000000 // gc decides
}

func main() {
	println("parenAssertions", parenAssertions())
	println("parenInstantiations", parenInstantiations())
	println("parenMethodExprsValues", parenMethodExprsValues())
}
