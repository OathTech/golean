package main

// Defect-neighbourhood campaign, shape S2 (conversions: a missing kernel arm or a
// value not retagged), lane sweep/s2-conversions, 2026-10-26: every row is an
// agreement with gc on a route no earlier row held (the matrix is on the member
// entries' Neighbourhood lines in docs/BUGS.md; the plan is
// docs/2026-10-27_defect-neighbourhood-campaign.md §4).
// []byte / []rune targets with defined element types and a literal operand at a
// defined slice type, and the idioms gc optimizes without an allocation
// (len([]rune(s)), string(b) == s, m[string(b)], switch string(b), the range and
// index forms, the append spread).

type MyByte byte
type MyRune rune
type MyBytes []byte

func bytesOfDefinedElem() (int, int, int) {
	s := "héllo"
	b := []MyByte(s)
	b[0] = 'H'
	return len(b), int(b[0]), int(b[1])
}

func definedBytesOfLiteral() (int, int, bool) {
	b := MyBytes("abc")
	c := MyBytes("abc")
	b[0] = 'x'
	return len(b), int(b[0]), c[0] == 'a'
}

func runesOfDefinedElem() (int, int, int) {
	s := "héllo\xff"
	r := []MyRune(s)
	return len(r), int(r[1]), int(r[5])
}

func bytesIdioms() (int, int, int, int) {
	s := "héllo"
	n := len([]byte(s))
	x := int([]byte(s)[1])
	sum := 0
	for i, b := range []byte(s) {
		sum += i + int(b)
	}
	b := []byte("x")
	b = append(b, []byte(s)...)
	return n, x, sum, len(b)
}

func runesIdioms() (int, int, int) {
	s := "héllo\xff"
	n := len([]rune(s))
	x := int([]rune(s)[1])
	sum := 0
	for i, r := range []rune(s) {
		sum += i*1000 + int(r)
	}
	return n, x, sum
}

func stringCompareIdiom() (bool, bool, bool) {
	b := []byte("abc")
	s := "abc"
	return string(b) == s, s == string(b), string(b) < "abd"
}

func mapIndexStringOfBytes() (int, int) {
	m := map[string]int{"abc": 7}
	b := []byte("abc")
	v := m[string(b)]
	m[string(b)] = 9
	return v, m["abc"]
}

func switchOnStringOfBytes() int {
	b := []byte("two")
	switch string(b) {
	case "one":
		return 1
	case "two":
		return 2
	}
	return 0
}

func main() {}
