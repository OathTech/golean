// Defect-neighbourhood campaign, shape S28 (spelling admission; members BUG-136/115, and
// BUG-287 fixed in train 26), lane sweep/s28-s29-spelling-symbols, 2026-11-05
// (docs/2026-10-27_defect-neighbourhood-campaign.md §4). Parenthesised composite-literal
// elements and keys, index and slice operands, and selector bases; expected = gc go1.26.5.

package main

type pt struct{ x, y int }

func (p pt) sum() int { return p.x + p.y }

func (p *pt) bump() int { p.x++; return p.x }

type inner struct{ v int }
type outer struct {
	inner
	name string
}

func mk() pt { return pt{5, 6} }

func parenLiteralElements() int {
	x, y := 1, 2
	s := []int{(1), (2), (x + y)}
	p := pt{(x), (y)}
	q := pt{x: (y), y: (x)}
	m := map[string]int{("a"): (1), ("b"): (2)}
	k := []int{(2): 1}
	a := [...]int{(1): 5}
	ps := []pt{{(7), (8)}}
	pp := &pt{(9), (10)}
	return s[2]*100000 + p.sum()*10000 + q.sum()*1000 + (m["a"]+m["b"])*100 + (len(k)+len(a))*10 + (ps[0].x + pp.y) // 333360+? (gc decides)
}

func parenIndexSlice() int {
	s := []int{10, 20, 30, 40}
	i, j := 1, 3
	a := [3]int{1, 2, 3}
	pa := &a
	m := map[string]int{"k": 7}
	str := "hey"
	n := s[(i)] + s[(i):(j)][0] + len(s[(i):]) + (s)[0] + (s)[1:2][0] + (m)["k"] + (a)[2] + (pa)[1] + int((str)[0]) + ((s))[3] + (s[1:3])[0] + len((s)[1:3:4])
	return n // 20+20+3+10+20+7+3+2+104+40+20+2 = 251
}

func parenSelectors() int {
	p := &pt{1, 2}
	s := []pt{{3, 4}}
	v := pt{5, 6}
	var i interface{ sum() int } = pt{7, 8}
	var any1 any = pt{9, 10}
	o := outer{inner{11}, "n"}
	n := (p).x + ((p)).y + (s[0]).x + (mk()).y + (v).sum() + (&v).bump() + (p).sum() + (pt{1, 1}).sum() + (any1.(pt)).x + (i).sum() + (o).inner.v + (o).v + ((o).inner).v
	return n // 1+2+3+6+11+6+3+2+9+15+11+11+11 = 91
}

func main() {
	println("parenLiteralElements", parenLiteralElements())
	println("parenIndexSlice", parenIndexSlice())
	println("parenSelectors", parenSelectors())
}
