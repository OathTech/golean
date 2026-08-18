package main

// spec#Representability block Representability-1-25bd0473: the
// representability table. Each row's constant is representable by the
// named type with the value the spec asserts:
//   'a' as byte == 97; 97 as rune == 97; "foo" as string;
//   1024 as int16; 42.0 as byte == 42; 1e10 as uint64 == 10000000000;
//   2.718281828459045 as float32 rounds to 2.7182817 (round-to-even);
//   -1e-1000 as float64 rounds to IEEE -0.0 which is "further
//   simplified to 0.0" (an UNSIGNED zero — the sign bit is clear);
//   0i as int == 0; (42 + 0i) as float32 == 42.0.
// Wrapped as variable declarations with these constant initializers
// (representability governs implicit conversion in both contexts).

func reprIntsAndStrings() (byte, rune, string, int16, byte, uint64) {
	var a byte = 'a'
	var r rune = 97
	var s string = "foo"
	var i int16 = 1024
	var b byte = 42.0
	var u uint64 = 1e10
	return a, r, s, i, b, u
}

func reprFloatRounding() float32 {
	var f float32 = 2.718281828459045
	return f // spec: rounds to 2.7182817
}

// -1e-1000 rounds to IEEE -0.0, then is simplified to unsigned 0.0:
// the stored value must compare equal to zero AND carry a CLEAR sign
// bit, observed as 1/f == +Inf (a -0.0 would give -Inf).
// Latitude note (P3 audit S7): float division by zero is "not specified
// beyond the IEEE 754 standard; whether a run-time panic occurs is
// implementation-specific" (spec#Floating_point_operators) — this probe
// relies on the registered R5 narrowing (latitude inventory §3), the
// same convention min-max-float-specials cites.
func reprNegTinyIsUnsignedZero() (bool, bool) {
	var f float64 = -1e-1000
	return f == 0, 1/f > 0
}

func reprComplexConstants() (int, float32) {
	var n int = 0i
	var f float32 = 42 + 0i
	return n, f
}

func main() {
	reprIntsAndStrings()
}
