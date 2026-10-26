package main

// Defect-neighbourhood campaign, shape S2 (conversions: a missing kernel arm or a
// value not retagged), lane sweep/s2-conversions, 2026-10-26: every row is an
// agreement with gc on a route no earlier row held (the matrix is on the member
// entries' Neighbourhood lines in docs/BUGS.md; the plan is
// docs/2026-10-27_defect-neighbourhood-campaign.md §4).
// String targets: string(i) for a DEFINED int and an int variable (negative,
// out of range, uint8, int64 — U+FFFD per the spec), and string over slices
// whose ELEMENT type is a defined byte/rune (the emitter routes by the element's
// underlying kind, as go/types does).

type Code int
type MyByte byte
type MyRune rune

func stringOfDefinedInt() (string, int) {
	c := Code(0x4E16)
	s := string(c)
	return s, len(s)
}

func stringOfIntVar() (string, int, int, int) {
	i := 65
	n := -1
	big := 0x110000
	var u8 uint8 = 200
	var i64 int64 = 0x1F600
	s := string(i) + string(n) + string(big) + string(u8) + string(i64)
	return s, len(s), len(string(n)), len(string(u8))
}

func stringOfDefinedByteElems() (string, int) {
	bs := []MyByte{'h', 'i', 0xC3, 0xA9}
	s := string(bs)
	return s, len(s)
}

func stringOfDefinedRuneElems() (string, int) {
	rs := []MyRune{'h', 0xE9, 0x1F600}
	s := string(rs)
	return s, len(s)
}

func main() {}
