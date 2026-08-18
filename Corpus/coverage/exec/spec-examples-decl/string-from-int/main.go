package main

// spec#Conversions_to_and_from_a_string_type block
// Conversions_to_and_from_a_string_type-5-e2a4cb7a: for historical reasons an
// integer value converts to a string holding the UTF-8 encoding of that code
// point — string('a') == "a", string(65) == "A", string('\xf8') == "\u00f8"
// — and values outside the valid code point range yield "\ufffd"
// (string(-1)). Also to a named string type: myString('\u65e5') == "\u65e5".

type myString string

func stringFromInt() string {
	s1 := string('a')        // "a"
	s2 := string(65)         // "A"
	s3 := string('\xf8')     // "\u00f8"
	s4 := string(-1)         // "\ufffd"
	s5 := myString('\u65e5') // "\u65e5"
	return s1 + "," + s2 + "," + s3 + "," + s4 + "," + string(s5)
}
