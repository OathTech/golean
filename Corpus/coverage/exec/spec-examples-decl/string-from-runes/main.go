package main

// spec#Conversions_to_and_from_a_string_type block
// Conversions_to_and_from_a_string_type-2-79d2a1ba: converting a rune slice
// to a string concatenates the UTF-8 encodings of the individual rune values
// — including through named slice types (runes), named element types
// (myRune), and to a named string type (myString).

type myString string

type runes []rune

type myRune rune

func stringFromRunes() string {
	s1 := string([]rune{0x767d, 0x9d6c, 0x7fd4}) // "\u767d\u9d6c\u7fd4"
	s2 := string([]rune{})                       // ""
	s3 := string([]rune(nil))                    // ""
	s4 := string(runes{0x767d, 0x9d6c, 0x7fd4})  // "\u767d\u9d6c\u7fd4"
	s5 := string([]myRune{0x266b, 0x266c})       // "\u266b\u266c"
	s6 := myString([]myRune{0x1f30e})            // "\U0001f30e"
	return s1 + "," + s2 + "," + s3 + "," + s4 + "," + s5 + "," + string(s6)
}
