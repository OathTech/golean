package main

// S4 sweep (lane sweep/s4-identity, 2026-10-26): BUG-121's mechanism (R19,
// gc's zero-copy `[]byte(s)` aliasing the string's bytes; the machine
// allocates a fresh backing per conversion, `convCapApplyAt`) at the routes
// beside strings/conv-identity/{ident-var,ident-lit}: a CONSTANT operand, a
// package-level string variable, the conversions bound to PARAMETERS, a
// SUBSTRING operand (`&b[1] == &c[0]`), a second variable holding the same
// string — gc `true`, the machine `false` (red rows on BUG-121's Cases line).
// Controls that agree at birth: `[]rune(s)` (gc always allocates), an escaped
// result, the round trip `[]byte(string(b))`, and two conversions of two
// CALL results (two strings, no sharing).

const konst = "hello"

var gstr = "hello"
var keepB []byte

func mkS(n int) string {
	s := ""
	for i := 0; i < n; i++ {
		s += "a"
	}
	return s
}

func bit(b bool, w int) int {
	if b {
		return w
	}
	return 0
}

func sameHead(x, y []byte) bool { return &x[0] == &y[0] }

// Two conversions of a constant (gc 1).
func convBytesConst() int {
	b := []byte(konst)
	c := []byte(konst)
	return bit(&b[0] == &c[0], 1)
}

// Two conversions of a package-level variable (gc 1).
func convBytesGlobalVar() int {
	d := []byte(gstr)
	e := []byte(gstr)
	return bit(&d[0] == &e[0], 1)
}

// Two conversions bound to parameters, a variable operand (gc 1).
func convBytesParams() int {
	s := mkS(5)
	return bit(sameHead([]byte(s), []byte(s)), 1)
}

// The same with a literal operand (gc 1).
func convBytesParamsLit() int {
	return bit(sameHead([]byte("hello"), []byte("hello")), 1)
}

// A substring operand: the conversion of `s[1:]` starts one byte into the
// conversion of `s` (gc 1; the heads differ, 0 at the tens).
func convBytesSubstring() int {
	s := mkS(5)
	b := []byte(s)
	c := []byte(s[1:])
	return bit(&b[1] == &c[0], 1) + bit(&b[0] == &c[0], 10)
}

// A second variable holding the same string value (gc 1).
func convBytesCopiedVar() int {
	s := mkS(5)
	t := s
	b := []byte(s)
	d := []byte(t)
	return bit(&b[0] == &d[0], 1)
}

// CONTROL (agrees): `[]rune(s)` twice, a variable and a literal (gc 0).
func convRunesTwice() int {
	s := mkS(3)
	r := []rune(s)
	q := []rune(s)
	r2 := []rune("hello")
	q2 := []rune("hello")
	return bit(&r[0] == &q[0], 1) + bit(&r2[0] == &q2[0], 10)
}

// CONTROL (agrees): a result that ESCAPES is a fresh copy (gc 0).
func convBytesEscaped() int {
	s := mkS(5)
	b := []byte(s)
	keepB = b
	c := []byte(s)
	return bit(&b[0] == &c[0], 1) + bit(&keepB[0] == &c[0], 10)
}

// CONTROL (agrees): the round trip `[]byte(string(b))` copies (gc 0).
func convBytesRoundtrip() int {
	b := []byte{'h', 'i'}
	c := []byte(string(b))
	d := []byte(string(b))
	return bit(&b[0] == &c[0], 1) + bit(&c[0] == &d[0], 10)
}

// CONTROL (agrees): two conversions of two CALL results are two strings (gc 0).
func convBytesCallOperand() int {
	b := []byte(mkS(4))
	c := []byte(mkS(4))
	return bit(&b[0] == &c[0], 1)
}

func main() {
	println(convBytesConst(), convBytesGlobalVar(), convBytesParams(), convBytesParamsLit(),
		convBytesSubstring(), convBytesCopiedVar(), convRunesTwice(), convBytesEscaped(),
		convBytesRoundtrip(), convBytesCallOperand())
}
