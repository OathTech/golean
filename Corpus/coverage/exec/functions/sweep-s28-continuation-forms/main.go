// Defect-neighbourhood campaign, shape S28 (spelling admission; members BUG-136/115, and
// BUG-287 fixed in train 26), lane sweep/s28-s29-spelling-symbols, 2026-11-05
// (docs/2026-10-27_defect-neighbourhood-campaign.md §4). Line continuations where the
// lexer inserts no semicolon: after a binary operator, a comma, a dot, an opening
// bracket, inside a for header, across a raw string, in parameter and result lists;
// expected = gc go1.26.5.

package main

type pt struct{ v int }

func (p pt) get() int { return p.v }

func add(a, b int) int { return a + b }

func mult(a, b,
	c int) int {
	return a * b * c
}

func retPair() (int,
	int) {
	return 1,
		2
}

func params(a int,
	b int,
) int {
	return a + b
}

func continuationForms() int {
	a, b := 1, 2
	n := a +
		b
	n += add(
		a,
		b,
	)
	s := []int{
		1,
		2,
	}
	p := pt{3}
	n += p.
		get()
	if a > 0 &&
		b > 0 {
		n += 10
	}
	for i := 0;
		i < 2;
		i++ {
		n += 100
	}
	str := "x"
	str = str +
		"y"
	raw := `line1
line2`
	n += len(str)*1000 + len(raw)*10000 + len(s)
	n += mult(
		a, b,
		3)
	c, d := retPair()
	n += params(c,
		d) * 100000
	m := map[string]int{
		"k": 1,
		"l": 2}
	n += len(m) * 1000000
	return n // 3+3+3+10+200+2000+110000+2+6+300000+2000000 = 2412227
}

func main() {
	println("continuationForms", continuationForms())
}
