package main

// Defect-neighbourhood campaign, shape S2 (conversions: a missing kernel arm or a
// value not retagged), lane sweep/s2-conversions, 2026-10-26: every row is an
// agreement with gc on a route no earlier row held (the matrix is on the member
// entries' Neighbourhood lines in docs/BUGS.md; the plan is
// docs/2026-10-27_defect-neighbourhood-campaign.md §4).
// Constant conversion forms: string(65) of an untyped constant (one rune, not
// digits), MyStr(65), int(3.0), MyInt(1e3), and a converted int as a map key
// and a switch tag at a defined type.

type MyStr string
type MyInt int

func stringOfConstInt() (string, int) {
	s := string(65) + string(0x1F600)
	return s, len(s)
}

func constantForms() (string, int, int, int) {
	s := MyStr(65)
	i := int(3.0)
	m := MyInt(1e3)
	x := 3
	keyed := map[MyInt]int{3: 7}[MyInt(x)]
	r := 0
	switch MyInt(x) {
	case 2:
		r = 1
	case 3:
		r = 2
	}
	return string(s), i, int(m), keyed*10 + r
}

func main() {}
