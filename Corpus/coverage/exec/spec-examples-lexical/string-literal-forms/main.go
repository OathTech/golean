// spec#String_literals block String_literals-3-01d5cea4
// The spec's five string literals that all represent the SAME string
// "日本語": UTF-8 source text (interpreted and raw), \u escapes,
// \U escapes, and explicit \x UTF-8 bytes. Pins their pairwise
// equality plus the byte length (9) and the exact first/middle/last
// UTF-8 bytes, so a mis-decoded escape or mis-encoded code point
// flips a score bit.
package main

func stringLiteralForms() int {
	s1 := "日本語"                                  // UTF-8 input text
	s2 := `日本語`                                  // UTF-8 input text as a raw literal
	s3 := "\u65e5\u672c\u8a9e"                   // the explicit Unicode code points
	s4 := "\U000065e5\U0000672c\U00008a9e"       // the explicit Unicode code points
	s5 := "\xe6\x97\xa5\xe6\x9c\xac\xe8\xaa\x9e" // the explicit UTF-8 bytes
	score := 0
	if s1 == s2 {
		score += 1
	}
	if s1 == s3 {
		score += 2
	}
	if s1 == s4 {
		score += 4
	}
	if s1 == s5 {
		score += 8
	}
	if len(s1) == 9 {
		score += 16
	}
	if s1[0] == 0xe6 && s1[4] == 0x9c && s1[8] == 0x9e {
		score += 32
	}
	return score
}

func main() {
	stringLiteralForms()
}
