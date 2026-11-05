package main

// Sweep lane sweep/s21-stdlib (2026-11-05), shape S21 — stdlib shims and source-through
// (the matrix is on the member entries' Neighbourhood lines in docs/BUGS.md, BUG-089/086/073/071/154/153;
// the plan is docs/2026-10-27_defect-neighbourhood-campaign.md §4). Every row: expected = gc go1.26.5.
// Group H13: math/bits at every width — the table-driven leaves (Len / LeadingZeros / TrailingZeros / OnesCount / Reverse /
// ReverseBytes), the rotations at every count class, the carry / borrow / double-width arithmetic (Div / Rem refuse by name:
// their panic values are runtime linknames).
import (
	"math/bits"
	"strconv"
)

func i(v int) string { return strconv.Itoa(v) }

func lenFamily() string {
	return i(bits.Len(0)) + i(bits.Len(1)) + i(bits.Len(18446744073709551615)) + "|" + i(bits.Len8(0)) + i(bits.Len8(0x80)) + i(bits.Len16(0x0100)) + i(bits.Len32(0xffffffff)) + i(bits.Len64(1<<63)) + "|" +
		i(bits.LeadingZeros(0)) + i(bits.LeadingZeros8(1)) + i(bits.LeadingZeros16(0)) + i(bits.LeadingZeros32(1)) + i(bits.LeadingZeros64(1)) + "|" +
		i(bits.TrailingZeros(0)) + i(bits.TrailingZeros8(0x80)) + i(bits.TrailingZeros16(0)) + i(bits.TrailingZeros32(8)) + i(bits.TrailingZeros64(1<<40)) + i(bits.TrailingZeros64(0))
}
func onesCount() string {
	return i(bits.OnesCount(0)) + i(bits.OnesCount(18446744073709551615)) + i(bits.OnesCount8(0xa5)) + i(bits.OnesCount16(0xffff)) + i(bits.OnesCount32(0x80000001)) + i(bits.OnesCount64(0x5555555555555555))
}
func rotate() string {
	return i(int(bits.RotateLeft8(0x81, 1))) + "," + i(int(bits.RotateLeft8(0x81, -1))) + "," + i(int(bits.RotateLeft8(0x81, 8))) + "," + i(int(bits.RotateLeft8(0x81, 9))) + "," + i(int(bits.RotateLeft8(0x81, -9))) + "|" +
		i(int(bits.RotateLeft16(0x8001, 4))) + "," + i(int(bits.RotateLeft32(0x80000001, -1))) + "," + strconv.FormatUint(bits.RotateLeft64(1, 63), 10) + "," + strconv.FormatUint(bits.RotateLeft64(1, 64), 10) + "," + strconv.FormatUint(uint64(bits.RotateLeft(1, -1)), 10) + "," + i(int(bits.RotateLeft8(0, 3)))
}
func reverseFamily() string {
	return i(int(bits.Reverse8(0x01))) + "," + i(int(bits.Reverse16(0x0001))) + "," + strconv.FormatUint(uint64(bits.Reverse32(0x00000001)), 10) + "," + strconv.FormatUint(bits.Reverse64(1), 10) + "," + strconv.FormatUint(uint64(bits.Reverse(1)), 10) + "|" +
		i(int(bits.ReverseBytes16(0x0102))) + "," + strconv.FormatUint(uint64(bits.ReverseBytes32(0x01020304)), 10) + "," + strconv.FormatUint(bits.ReverseBytes64(0x0102030405060708), 10) + "," + strconv.FormatUint(uint64(bits.ReverseBytes(1)), 10)
}
func addSubMul() string {
	s1, c1 := bits.Add64(1<<63, 1<<63, 1)
	s2, c2 := bits.Add32(0xffffffff, 1, 0)
	s3, c3 := bits.Add(18446744073709551615, 0, 1)
	d1, b1 := bits.Sub64(0, 1, 0)
	d2, b2 := bits.Sub32(5, 3, 1)
	d3, b3 := bits.Sub(0, 0, 1)
	h1, l1 := bits.Mul64(1<<63, 4)
	h2, l2 := bits.Mul32(0xffffffff, 0xffffffff)
	h3, l3 := bits.Mul(18446744073709551615, 18446744073709551615)
	u := strconv.FormatUint
	return u(s1, 10) + "/" + u(c1, 10) + "|" + u(uint64(s2), 10) + "/" + u(uint64(c2), 10) + "|" + u(uint64(s3), 10) + "/" + u(uint64(c3), 10) + "|" + u(d1, 10) + "/" + u(b1, 10) + "|" + u(uint64(d2), 10) + "/" + u(uint64(b2), 10) + "|" + u(uint64(d3), 10) + "/" + u(uint64(b3), 10) + "|" + u(h1, 10) + "/" + u(l1, 10) + "|" + u(uint64(h2), 10) + "/" + u(uint64(l2), 10) + "|" + u(uint64(h3), 10) + "/" + u(uint64(l3), 10)
}

func main() {
	lenFamily()
	onesCount()
	rotate()
	reverseFamily()
	addSubMul()
}
