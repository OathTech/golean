// noodler probes — conversions at the edges of the spec's text
// (spec#Conversions, spec#Conversions_to_and_from_a_string_type,
// spec#Numeric_types). Every subject returns a checksum or a small
// tuple; nothing prints.
package main

// surrogate / out-of-range / negative rune values convert to "�"
// (spec#Conversions_to_and_from_a_string_type: "values outside the
// range of valid Unicode code points are converted to "�"").
func stringFromBadRunes() (int, int, int, int) {
	surrogate := rune(0xD800)
	tooBig := rune(0x110000)
	negative := rune(-1)
	maxValid := rune(0x10FFFF)
	return len(string(surrogate)), len(string(tooBig)), len(string(negative)), len(string(maxValid))
}

func stringFromBadRunesBytes() string {
	surrogate := rune(0xDFFF)
	s := string(surrogate)
	return s
}

// []rune over invalid UTF-8: each bad byte decodes to U+FFFD.
func runesFromInvalidUTF8() (int, int, int, int) {
	s := "\xff\xfea"
	r := []rune(s)
	return len(r), int(r[0]), int(r[1]), int(r[2])
}

// truncated multi-byte sequence: each byte is its own U+FFFD.
func runesFromTruncatedSequence() (int, int) {
	s := "\xe2\x82" // first two bytes of U+20AC
	r := []rune(s)
	full := []rune("\xe2\x82\xac")
	return len(r), len(full)
}

// overlong encoding of NUL (C0 80) and an encoded surrogate (ED A0 80)
// are invalid: every byte decodes separately.
func runesFromOverlongAndSurrogateBytes() (int, int) {
	over := []rune("\xc0\x80")
	surr := []rune("\xed\xa0\x80")
	return len(over), len(surr)
}

// string([]rune) with a surrogate inside: that element becomes "�".
func stringFromRuneSliceWithSurrogate() (string, int) {
	r := []rune{0x41, 0xD800, 0x42}
	s := string(r)
	return s, len(s)
}

// range over a string with a bad byte yields U+FFFD with width 1.
func rangeInvalidByteWidths() (int, int) {
	s := "a\xffb"
	count, sum := 0, 0
	for i, r := range s {
		count++
		sum += i*1000 + int(r)
	}
	return count, sum
}

// Conversion from string to []byte / []rune always yields a NON-nil
// slice, even for "" (spec: "yields a non-nil slice").
func emptyStringToBytesIsNonNil() (bool, bool, int, int) {
	var s string
	b := []byte(s)
	r := []rune(s)
	return b == nil, r == nil, len(b), len(r)
}

// string of a nil []byte / nil []rune is "".
func nilSlicesToString() (string, string, bool) {
	var b []byte
	var r []rune
	return string(b), string(r), string(b) == ""
}

// string(int-kinded variable) is legal (vet-flagged, not a language
// error): the value is treated as a rune.
func stringOfIntKinds() (string, string, string, int) {
	var i int = 0x1F600
	var b byte = 200
	var i64 int64 = 65
	return string(rune(i)), string(rune(b)), string(rune(i64)), len(string(rune(b)))
}

// float -> int truncates toward zero; -0.0 -> 0.
func floatToIntTruncation() (int, int, int, int64) {
	a, b := -2.7, 2.7
	var negZero float64 = 0
	negZero = -negZero
	var half float32 = -0.5
	return int(a), int(b), int(negZero), int64(half)
}

// int -> float rounds to nearest even at the precision boundary.
func intToFloatRounding() (float32, float64, float64, bool) {
	var i int = 16777217 // 2^24 + 1: not representable in float32
	var j int64 = 1<<53 + 1
	var u uint64 = 1<<64 - 1
	return float32(i), float64(j), float64(u), float64(float32(i)) == 16777216
}

// float32 arithmetic at runtime vs the same expression as constants.
func float32VsConstantArithmetic() (bool, bool, bool) {
	var a, b, c float32 = 0.1, 0.2, 0.3
	const ca, cb, cc = 0.1, 0.2, 0.3
	var x, y, z float64 = 0.1, 0.2, 0.3
	return a+b == c, ca+cb == cc, x+y == z
}

// Narrowing integer conversions wrap (two's complement).
func narrowingWraps() (uint8, uint32, int8, int16, uint64) {
	x := -1
	y := 200
	z := 40000
	return uint8(x), uint32(x), int8(y), int16(z), uint64(x)
}

// uint8(float64) in range truncates; large-in-range paths.
func floatToUnsignedInRange() (uint8, uint16, uint64) {
	a := 255.9
	b := 65535.4
	c := 1.8e19 // below 2^64
	return uint8(a), uint16(b), uint64(c)
}

// byte-wise string comparison: an invalid byte compares by value.
func stringCompareInvalidBytes() (bool, bool, bool) {
	a := "\xff"
	b := "ÿ" // C3 BF
	c := "\xc3"
	return a > b, c < b, a > c
}

// Defined string / byte-slice types convert both ways.
type MyString string
type MyBytes []byte

func definedStringByteConversions() (int, string, bool) {
	s := MyString("héllo")
	b := MyBytes(s)
	back := MyString(b)
	return len(b), string(back), back == s
}

// A slice-to-array conversion of a nil slice into [0]T is fine.
func nilSliceToZeroArray() int {
	var s []int
	a := [0]int(s)
	return len(a)
}

// int -> string-ish via strconv-like manual path: rune arithmetic on
// a byte.
func runeArithmeticToString() (string, string) {
	c := 'a'
	return string(c + 1), string(rune('A' + 25))
}

// float64 -> float32 -> float64 loses low bits deterministically.
func floatNarrowRoundTrip() (bool, float64) {
	x := 0.1
	y := float64(float32(x))
	return x == y, y - x
}

// uint64 -> float32 rounding of a large value; then back to uint64 stays
// in range.
func bigUnsignedToFloat32() (float32, uint64) {
	var u uint64 = 1<<63 + 1
	f := float32(u)
	return f, uint64(f)
}

// integer -> float with exactly-halfway ties round to even.
func tiesToEven() (float32, float32) {
	var a int32 = 16777219 // 2^24 + 3 -> halfway between 16777218 and 16777220
	var b int32 = 16777221 // halfway between 16777220 and 16777222
	return float32(a), float32(b)
}

func main() {}
