package main

// Sweep lane sweep/s22-readout (2026-11-07), shape S22 — the readout (the matrix is on the member entries'
// Neighbourhood lines in docs/BUGS.md, BUG-013/019/065/072/093/106/107/114; the plan is
// docs/2026-10-27_defect-neighbourhood-campaign.md §4). Every row: expected = gc go1.26.5.
// Group A1/A2: the `int` observation carries the reflect KIND name ("int8" … "uint64") and never the defined
// type's name; byte is uint8 and rune is int32; bool carries no type identity either.

type K8 int8
type K16 int16
type K32 int32
type K64 int64
type K int
type U8 uint8
type U16 uint16
type U32 uint32
type U64 uint64
type U uint
type Flag bool

func signedKindsMin() (K8, K16, K32, K64, K) {
	return -128, -32768, -2147483648, -9223372036854775808, -9223372036854775808
}
func signedKindsMax() (K8, K16, K32, K64, K) {
	return 127, 32767, 2147483647, 9223372036854775807, 9223372036854775807
}
func unsignedKindsMax() (U8, U16, U32, U64, U) {
	return 255, 65535, 4294967295, 18446744073709551615, 18446744073709551615
}
func unsignedKindsZero() (U8, U16, U32, U64, U) {
	var a U8
	var b U16
	var c U32
	var d U64
	var e U
	return a, b, c, d, e
}
func byteRuneAliases() (byte, rune, [2]byte, [1]rune) {
	return 'a', 'é', [2]byte{1, 255}, [1]rune{-1}
}
func boolsDefined() (bool, Flag, [2]Flag) {
	return true, Flag(false), [2]Flag{true, false}
}
func minusOneEverySigned() (K8, K16, K32, K64, K, int8, int16, int32, int64, int) {
	return -1, -1, -1, -1, -1, -1, -1, -1, -1, -1
}

func main() {
	signedKindsMin()
	signedKindsMax()
	unsignedKindsMax()
	unsignedKindsZero()
	byteRuneAliases()
	boolsDefined()
	minusOneEverySigned()
}
