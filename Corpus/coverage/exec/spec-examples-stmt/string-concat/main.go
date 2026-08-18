package main

// spec#String_concatenation block String_concatenation-1-994ecb2e:
// "Strings can be concatenated using the + operator or the +=
// assignment operator"; "String addition creates a new string by
// concatenating the operands." With c == '!' (rune 33):
// s := "hi" + string(c) yields "hi!", then s += " and good bye"
// yields "hi! and good bye". The new-string claim is pinned by the
// original operand surviving unchanged.

func stringConcatForms() (string, string) {
	c := '!'
	base := "hi"
	s := base + string(c)
	s += " and good bye"
	return s, base // base is unchanged: + created a NEW string
}

func main() {
	stringConcatForms()
}
