package main

// Defect-neighbourhood campaign, shape S2 (conversions: a missing kernel arm or a
// value not retagged), lane sweep/s2-conversions, 2026-10-26: every row is an
// agreement with gc on a route no earlier row held (the matrix is on the member
// entries' Neighbourhood lines in docs/BUGS.md; the plan is
// docs/2026-10-27_defect-neighbourhood-campaign.md §4).
// Parenthesised conversion spellings (the type, the operand, both) on every
// route the emitter distinguishes (struct, pointer, bytes, string, runes, defined
// int, int, float) — the S28 spelling axis on this shape.

type A struct{ X int }
type B struct{ X int }
type MyInt int

func parenSpellings() int {
	a := A{1}
	b := (B)(a)
	c := B((a))
	p := (*B)((&a))
	bs := ([]byte)("hi")
	s := (string)(bs)
	r := ([]rune)(s)
	n := (MyInt)(len(r))
	i := (int)(n)
	f := (float64)(i)
	return b.X*100000 + c.X*10000 + p.X*1000 + len(bs)*100 + len(s)*10 + int(f)
}

func main() {}
