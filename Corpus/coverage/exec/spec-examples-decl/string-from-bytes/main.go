package main

// spec#Conversions_to_and_from_a_string_type block
// Conversions_to_and_from_a_string_type-1-7a8a44d8: converting a byte slice
// (or any type whose elements' underlying type is byte) to a string yields a
// string whose bytes are the slice elements — including through named slice
// types (bytes), named element types (myByte), and to a named string type
// (myString). Empty and nil slices yield "". myString is the section's named
// string type.

type myString string

type bytes []byte

type myByte byte

func stringFromBytes() string {
	s1 := string([]byte{'h', 'e', 'l', 'l', '\xc3', '\xb8'}) // "hell\u00f8"
	s2 := string([]byte{})                                   // ""
	s3 := string([]byte(nil))                                // ""
	s4 := string(bytes{'h', 'e', 'l', 'l', '\xc3', '\xb8'})  // "hell\u00f8"
	s5 := string([]myByte{'w', 'o', 'r', 'l', 'd', '!'})     // "world!"
	s6 := myString([]myByte{'\xf0', '\x9f', '\x8c', '\x8d'}) // the globe emoji
	return s1 + "," + s2 + "," + s3 + "," + s4 + "," + s5 + "," + string(s6)
}
