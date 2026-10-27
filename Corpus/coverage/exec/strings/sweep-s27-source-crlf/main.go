package main

// Defect-neighbourhood campaign, shape S27 (byte transparency of
// string-carrying channels), lane sweep/s27-bytes, 2026-10-27: every row is an
// agreement with gc on a route no earlier row held (the matrix is on the member
// entries' Neighbourhood lines in docs/BUGS.md, BUG-105 and BUG-138; the plan is
// docs/2026-10-27_defect-neighbourhood-campaign.md §4).
// A7.2 / A2.2: CRLF line endings; the raw literal below holds a CR LF
// pair, which the lexer strips to LF (spec#String_literals), and an interpreted
// literal spells the same pair with escapes.

func crlfRawLiteral() (int, int, string, byte, byte) {
	raw := `a
b`
	esc := "a\r\nb"
	return len(raw), len(esc), raw, raw[1], esc[1]
}

func main() {
	crlfRawLiteral()
}
