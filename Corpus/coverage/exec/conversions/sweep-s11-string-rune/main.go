package main

// Sweep lane sweep/s11-kinds (2026-11-05), shape S11, group O: the RUN-TIME conversion of an
// integer to a string (spec#Conversions_to_and_from_a_string_type: the UTF-8 encoding of the code
// point; a value outside the valid range — negative, a surrogate, above 0x10FFFF — yields "�")
// at every code-point boundary and from every integer kind (a byte value 200 is the TWO-byte
// encoding of U+00C8, not the byte), to a defined string type, through a generic type parameter.
// The constant forms are folded by gc (spec-examples-decl/string-from-int); these are variables.

type dInt int
type myString string

func toStr[T ~int32 | ~int | ~uint64](x T) string { return string(x) }

func stringOfRuneBoundaries() (string, string, string, string, string, string, string, string) {
	var a rune = -1
	var b rune = 0
	var c rune = 0x7F
	var d rune = 0x80
	var e rune = 0x7FF
	var f rune = 0x800
	var g rune = 0xD7FF
	var h rune = 0xD800
	return string(a), string(b), string(c), string(d), string(e), string(f), string(g), string(h)
}

func stringOfRuneHigh() (string, string, string, string, string, string, string, string, string) {
	var a rune = 0xDFFF
	var b rune = 0xE000
	var c rune = 0xFFFD
	var d rune = 0xFFFF
	var e rune = 0x10000
	var f rune = 0x10FFFF
	var g rune = 0x110000
	var h rune = 2147483647
	var i rune = -2147483648
	return string(a), string(b), string(c), string(d), string(e), string(f), string(g), string(h), string(i)
}

func stringOfOtherKinds() (string, string, string, string, string, string, string, string, string) {
	var a int = 0x1F600
	var b int64 = 1 << 40
	var c uint64 = 1 << 63
	var d uint8 = 200
	var e uint16 = 0xFFFF
	var f dInt = 65
	var g int8 = -1
	var h uint32 = 0x110000
	var i uintptr = 0x10FFFF
	return string(a), string(b), string(c), string(d), string(e), string(f), string(g), string(h), string(i)
}

func stringOfRuneToDefined() (myString, myString, string, int) {
	var r rune = 0x65E5
	var bad rune = -1
	s := myString(r)
	return s, myString(bad), string(myString(bad)), len(myString(r))
}

func stringOfRuneGeneric() (string, string, string, int) {
	var a rune = 0x10FFFF
	var b int = 0x110000
	var c uint64 = 65
	return toStr(a), toStr(b), toStr(c), len(toStr(dInt(0xD800)))
}

func main() {
	stringOfRuneBoundaries()
	stringOfRuneHigh()
	stringOfOtherKinds()
	stringOfRuneToDefined()
	stringOfRuneGeneric()
}
