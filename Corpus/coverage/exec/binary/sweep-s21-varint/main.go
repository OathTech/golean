package main

// Sweep lane sweep/s21-stdlib (2026-11-05), shape S21 — stdlib shims and source-through
// (the matrix is on the member entries' Neighbourhood lines in docs/BUGS.md, BUG-089/086/073/071/154/153;
// the plan is docs/2026-10-27_defect-neighbourhood-campaign.md §4). Every row: expected = gc go1.26.5.
// Group H11: the varint codec — PutUvarint / Uvarint / AppendUvarint / PutVarint / Varint / AppendVarint at the length
// boundaries, the overflow and truncation returns.
import (
	"encoding/binary"
	"strconv"
)

func hex(b []byte) string {
	const d = "0123456789abcdef"
	out := ""
	for _, c := range b {
		out += string(d[c>>4]) + string(d[c&15])
	}
	return out
}
func uvarintRoundtrip() string {
	out := ""
	for _, v := range []uint64{0, 1, 127, 128, 300, 16383, 16384, 1 << 32, 18446744073709551615} {
		b := make([]byte, binary.MaxVarintLen64)
		n := binary.PutUvarint(b, v)
		got, m := binary.Uvarint(b[:n])
		out += hex(b[:n]) + "/" + strconv.Itoa(n) + "/" + strconv.FormatUint(got, 10) + "/" + strconv.Itoa(m) + ";"
	}
	return out
}
func varintRoundtrip() string {
	out := ""
	for _, v := range []int64{0, -1, 1, -64, 63, 64, -65, -9223372036854775808, 9223372036854775807} {
		b := make([]byte, binary.MaxVarintLen64)
		n := binary.PutVarint(b, v)
		got, m := binary.Varint(b[:n])
		out += hex(b[:n]) + "/" + strconv.Itoa(n) + "/" + strconv.FormatInt(got, 10) + "/" + strconv.Itoa(m) + ";"
	}
	return out
}
func overflowAndTruncated() string {
	o1, n1 := binary.Uvarint([]byte{0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x01})
	o2, n2 := binary.Uvarint([]byte{0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x02})
	o3, n3 := binary.Uvarint([]byte{0x80})
	o4, n4 := binary.Uvarint(nil)
	o5, n5 := binary.Varint([]byte{0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x01})
	o6, n6 := binary.Varint([]byte{0xff})
	return strconv.FormatUint(o1, 10) + "/" + strconv.Itoa(n1) + "|" + strconv.FormatUint(o2, 10) + "/" + strconv.Itoa(n2) + "|" + strconv.FormatUint(o3, 10) + "/" + strconv.Itoa(n3) + "|" + strconv.FormatUint(o4, 10) + "/" + strconv.Itoa(n4) + "|" + strconv.FormatInt(o5, 10) + "/" + strconv.Itoa(n5) + "|" + strconv.FormatInt(o6, 10) + "/" + strconv.Itoa(n6)
}
func appendVarints() string {
	a := binary.AppendUvarint([]byte("u:"), 300)
	a = binary.AppendVarint(a, -300)
	a = binary.AppendUvarint(a, 0)
	return hex(a) + "|" + strconv.Itoa(len(a)) + "|" + strconv.Itoa(binary.MaxVarintLen16) + strconv.Itoa(binary.MaxVarintLen32) + strconv.Itoa(binary.MaxVarintLen64)
}

func main() {
	uvarintRoundtrip()
	varintRoundtrip()
	overflowAndTruncated()
	appendVarints()
}
