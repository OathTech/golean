package main

// S18 sweep — the conversion capacity envelope (ChoiceSite.convCap, convCapMembers in
// Ops.lean; latitude inventory R3) at the lengths where it is a SINGLETON: a bound-1
// consult pops nothing, so these are strict rows. Bytes: n = 32 (the buffer, R(n) and n
// coincide) and every n > 32 that is itself a size class (48, 1024) or a page multiple
// (32768); runes: n ∈ {31, 32} (R(4n)/4 = 32) and every n > 32 (255, 256, 257 across the
// 1024-byte table boundary; 8191, 8193 across the 32760-byte page threshold); the literal
// regime (a 40-byte literal, folded constants, defined-type constants and targets). Probe-
// verified go1.26.5, 2026-10-27: gc plain = gc -race = the one member on every row.
var sinkB []byte
var sinkR []rune

type MyS string
type MyB []byte

const k = "hello"
const k2 = "world"

// A non-literal string of n bytes, built by doubling (no stdlib call, no pick).
//
//go:noinline
func mkN(n int) string {
	s := "a"
	for len(s) < n {
		s += s
	}
	return s[:n]
}

// A non-literal string of n two-byte runes.
//
//go:noinline
func mkE(n int) string {
	s := "é"
	for len(s) < 2*n {
		s += s
	}
	return s[:2*n]
}

// A non-literal string of n invalid bytes (each decodes as U+FFFD: n runes).
//
//go:noinline
func mkX(n int) string {
	s := "\xff"
	for len(s) < n {
		s += s
	}
	return s[:n]
}

// n = 32: the 32-byte buffer, R(32) = 32 and n coincide — the envelope is the singleton {32} (a bound-1 consult, strict); gc 32
func bytes32Mut() int {
	s := mkN(32)
	b := []byte(s)
	b[0] = 'x'
	return cap(b)
}

// n = 32 escaping: roundupsize(32) = 32 = n, singleton {32}
func bytes32Esc() int {
	s := mkN(32)
	b := []byte(s)
	sinkB = b
	return cap(b)
}

// n = 48 > 32, a size class: R(48) = 48 = n, singleton {48}; gc 48 (written, non-escaping → the roundupsize regime)
func bytes48Mut() int {
	s := mkN(48)
	b := []byte(s)
	b[0] = 'x'
	return cap(b)
}

// n = 1024, the first class of the 128-byte table: R(1024) = 1024, singleton; gc 1024
func bytes1024Esc() int {
	s := mkN(1024)
	b := []byte(s)
	sinkB = b
	return cap(b)
}

// n = 32768 = MaxSmallSize: a large object rounds to the page, 32768 = 4 pages: singleton {32768}; gc 32768
func bytes32768Esc() int {
	s := mkN(32768)
	b := []byte(s)
	sinkB = b
	return cap(b)
}

// a 40-byte LITERAL operand (gc walkStringToBytes: a [40]byte, stack or new): cap n even above 32 and even written; singleton {40}
func bytesLit40Mut() int {
	b := []byte("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa")
	b[0] = 'x'
	return cap(b)
}

// a concatenation of two CONSTANTS folds to a literal operand on both sides: {10}; gc 10 even written
func bytesConstConcatMut() int {
	b := []byte(k + k2)
	b[0] = 'x'
	return cap(b)
}

// string(rune(65)) is a constant string ("A"): the literal regime, {1}; gc 1
func bytesConstRuneMut() int {
	b := []byte(string(rune(65)))
	b[0] = 'x'
	return cap(b)
}

// a constant of a DEFINED string type is still the literal operand: {5}; gc 5
func bytesDefinedConstMut() int {
	b := []byte(MyS(k))
	b[0] = 'x'
	return cap(b)
}

// a constant converted to a DEFINED byte-slice type: the literal regime, {5}; gc 5
func bytesDefinedTargetConst() int {
	b := MyB(k)
	b[0] = 'x'
	return cap(b)
}

// n = 31 ≤ 32: the 32-rune buffer and R(124)/4 = 128/4 = 32 coincide — the singleton {32}; gc 32
func runes31Nomut() int {
	s := mkN(31)
	r := []rune(s)
	return cap(r)
}

// n = 31 escaping: roundupsize(124) = 128 → 32; singleton {32}
func runes31Esc() int {
	s := mkN(31)
	r := []rune(s)
	sinkR = r
	return cap(r)
}

// n = 32: the buffer's own size and R(128)/4 = 32; singleton {32}
func runes32Nomut() int {
	s := mkN(32)
	r := []rune(s)
	return cap(r)
}

// n = 40 > 32: R(160)/4 = 40 = n; singleton {40}
func runes40Esc() int {
	s := mkN(40)
	r := []rune(s)
	sinkR = r
	return cap(r)
}

// n = 64 non-escaping but past the buffer: R(256)/4 = 64; singleton {64}
func runes64Nomut() int {
	s := mkN(64)
	r := []rune(s)
	return cap(r)
}

// n = 255: 1020 bytes → the 128-byte table's first class 1024 → 256; singleton {256}
func runes255Esc() int {
	s := mkN(255)
	r := []rune(s)
	sinkR = r
	return cap(r)
}

// n = 256: 1024 bytes, a class: {256}
func runes256Nomut() int {
	s := mkN(256)
	r := []rune(s)
	return cap(r)
}

// n = 257: 1028 bytes → class 1152 → 288; singleton {288}
func runes257Esc() int {
	s := mkN(257)
	r := []rune(s)
	sinkR = r
	return cap(r)
}

// n = 8191: 32764 bytes > MaxSmallSize − 8 → the page path: 32768 bytes → 8192; singleton {8192}
func runes8191Esc() int {
	s := mkN(8191)
	r := []rune(s)
	sinkR = r
	return cap(r)
}

// n = 8193: 32772 bytes → 5 pages = 40960 → 10240; singleton {10240}
func runes8193Nomut() int {
	s := mkN(8193)
	r := []rune(s)
	return cap(r)
}

// n counts RUNES, not bytes: 33 two-byte runes (66 bytes) → R(132)/4 = 144/4 = 36; singleton {36}
func runesE33Esc() int {
	s := mkE(33)
	r := []rune(s)
	sinkR = r
	return cap(r)
}

// 40 invalid bytes decode as 40 U+FFFD runes: R(160)/4 = 40; singleton {40}
func runesX40Nomut() int {
	s := mkX(40)
	r := []rune(s)
	return cap(r)
}

// a constant of a defined string type to []rune: the literal regime {5}; gc 5
func runesDefinedConst() int {
	const c MyS = "héllo"
	r := []rune(c)
	return cap(r)
}
