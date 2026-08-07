package main

// ++/-- on DEFINED integer types (BUG-042, grossmith seed 559): the
// IncDec desugar's synthetic 1 literal must take the operand's
// UNDERLYING kind, resolved through the named type — with the wire
// carrying {"kind":"named"} the decoder's literal-kind lookup fell to
// the default int, so defInt8(5)++ desugared to an int8 + int add and
// went stuck ("mismatched + integer kinds: int8 and int"). Matrix:
// inc AND dec, signed AND unsigned underlying, with and without wrap,
// plus the unnamed control that never failed (the plain-int8 PASS is
// what localizes the defect to named-type resolution).

type defInt8 int8
type defUint8 uint8

func definedIncSigned() int8 {
	v := defInt8(5)
	v++
	return int8(v)
}

func definedDecSigned() int8 {
	v := defInt8(5)
	v--
	return int8(v)
}

func definedIncUnsigned() int {
	v := defUint8(5)
	v++
	return int(v)
}

func definedDecUnsigned() int {
	v := defUint8(5)
	v--
	return int(v)
}

func definedIncSignedWrap() int8 {
	v := defInt8(127)
	v++ // wraps to -128 (two's complement, spec §Integer overflow)
	return int8(v)
}

func definedDecSignedWrap() int8 {
	v := defInt8(-128)
	v-- // wraps to 127
	return int8(v)
}

func definedIncUnsignedWrap() int {
	v := defUint8(255)
	v++ // wraps to 0
	return int(v)
}

func definedDecUnsignedWrap() int {
	v := defUint8(0)
	v-- // wraps to 255
	return int(v)
}

func unnamedControl() int8 {
	v := int8(5)
	v++
	return int8(v)
}

func main() {
	definedIncSigned()
	definedDecSigned()
	definedIncUnsigned()
	definedDecUnsigned()
	definedIncSignedWrap()
	definedDecSignedWrap()
	definedIncUnsignedWrap()
	definedDecUnsignedWrap()
	unnamedControl()
}
