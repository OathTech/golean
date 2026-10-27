package main

// Sweep lane sweep/s10-panics (2026-10-27), shape S10: integer division and
// modulo by a RUN-TIME zero at every integer kind (spec#Integer_operators: «If
// the divisor is zero at run time, a run-time panic occurs»; gc's panicdivide
// text is kind-independent), at a defined type, in compound form, with a
// constant dividend, under recover; and the NO-panic control: the most negative
// value divided by -1 wraps at every signed kind (the int8 instance is
// ints/division-overflow). The zero arrives as the entry argument so no
// constant folding can see it.

type divDefined int16

func divInt8(z int) int {
	x := int8(7)
	y := int8(z)
	return int(x / y)
}

func modInt8(z int) int {
	x := int8(7)
	y := int8(z)
	return int(x % y)
}

func divInt16(z int) int {
	x := int16(7)
	y := int16(z)
	return int(x / y)
}

func modInt16(z int) int {
	x := int16(7)
	y := int16(z)
	return int(x % y)
}

func divInt32(z int) int {
	x := int32(7)
	y := int32(z)
	return int(x / y)
}

func modInt32(z int) int {
	x := int32(7)
	y := int32(z)
	return int(x % y)
}

func divInt64(z int) int {
	x := int64(7)
	y := int64(z)
	return int(x / y)
}

func modInt64(z int) int {
	x := int64(7)
	y := int64(z)
	return int(x % y)
}

func divUint(z int) int {
	x := uint(7)
	y := uint(z)
	return int(x / y)
}

func modUint(z int) int {
	x := uint(7)
	y := uint(z)
	return int(x % y)
}

func divUint8(z int) int {
	x := uint8(7)
	y := uint8(z)
	return int(x / y)
}

func modUint8(z int) int {
	x := uint8(7)
	y := uint8(z)
	return int(x % y)
}

func divUint16(z int) int {
	x := uint16(7)
	y := uint16(z)
	return int(x / y)
}

func modUint16(z int) int {
	x := uint16(7)
	y := uint16(z)
	return int(x % y)
}

func divUint32(z int) int {
	x := uint32(7)
	y := uint32(z)
	return int(x / y)
}

func modUint32(z int) int {
	x := uint32(7)
	y := uint32(z)
	return int(x % y)
}

func divUint64(z int) int {
	x := uint64(7)
	y := uint64(z)
	return int(x / y)
}

func modUint64(z int) int {
	x := uint64(7)
	y := uint64(z)
	return int(x % y)
}

func divUintptr(z int) int {
	x := uintptr(7)
	y := uintptr(z)
	return int(x / y)
}

func modUintptr(z int) int {
	x := uintptr(7)
	y := uintptr(z)
	return int(x % y)
}

func divDefinedKind(z int) int {
	x := divDefined(9)
	y := divDefined(z)
	return int(x / y)
}

func modDefinedKind(z int) int {
	x := divDefined(9)
	y := divDefined(z)
	return int(x % y)
}

func divAssign(z int) int {
	x := 9
	x /= z
	return x
}

func modAssign(z int) int {
	x := 9
	x %= z
	return x
}

func constDividend(z int) int {
	return 7 / z
}

// MinInt / -1 == MinInt and MinInt % -1 == 0 at every signed kind: no panic.
// gc: 4 kinds × (quotient equals the minimum, remainder zero) = 44.
func minOverNegOneKinds(z int) int {
	m := z // -1
	score := 0
	var a int16 = -32768
	if a/int16(m) == a {
		score += 1
	}
	if a%int16(m) == 0 {
		score += 10
	}
	var b int32 = -2147483648
	if b/int32(m) == b {
		score += 1
	}
	if b%int32(m) == 0 {
		score += 10
	}
	var c int64 = -9223372036854775808
	if c/int64(m) == c {
		score += 1
	}
	if c%int64(m) == 0 {
		score += 10
	}
	var d int = -9223372036854775808
	if d/m == d {
		score += 1
	}
	if d%m == 0 {
		score += 10
	}
	return score
}

func divRecovered(z int) int {
	r := 0
	func() {
		defer func() {
			if recover() != nil {
				r = 100
			}
		}()
		r = 9 / z
	}()
	return r + 1
}

func main() {}
