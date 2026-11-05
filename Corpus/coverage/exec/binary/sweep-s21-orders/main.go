package main

// Sweep lane sweep/s21-stdlib (2026-11-05), shape S21 — stdlib shims and source-through
// (the matrix is on the member entries' Neighbourhood lines in docs/BUGS.md, BUG-089/086/073/071/154/153;
// the plan is docs/2026-10-27_defect-neighbourhood-campaign.md §4). Every row: expected = gc go1.26.5.
// Group H11: the three byte orders (LittleEndian / BigEndian / NativeEndian) through every width, the Put* / Append*
// families, the orders' String / GoString, dispatch through the ByteOrder and AppendByteOrder interfaces.
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
func u(v uint64) string { return strconv.FormatUint(v, 10) }

func allOrdersUint() string {
	b := []byte{1, 2, 3, 4, 5, 6, 7, 8, 9}
	return u(uint64(binary.LittleEndian.Uint16(b))) + "," + u(uint64(binary.LittleEndian.Uint32(b))) + "," + u(binary.LittleEndian.Uint64(b)) + "|" +
		u(uint64(binary.BigEndian.Uint16(b))) + "," + u(uint64(binary.BigEndian.Uint32(b))) + "," + u(binary.BigEndian.Uint64(b)) + "|" +
		u(uint64(binary.NativeEndian.Uint16(b))) + "," + u(uint64(binary.NativeEndian.Uint32(b))) + "," + u(binary.NativeEndian.Uint64(b[1:]))
}
func putFamily() string {
	b := make([]byte, 8)
	binary.LittleEndian.PutUint16(b, 0x0102)
	binary.BigEndian.PutUint16(b[2:], 0x0102)
	s1 := hex(b)
	binary.LittleEndian.PutUint32(b, 0x01020304)
	binary.BigEndian.PutUint32(b[4:], 0x01020304)
	s2 := hex(b)
	binary.NativeEndian.PutUint64(b, 0x0102030405060708)
	s3 := hex(b)
	binary.BigEndian.PutUint64(b, 18446744073709551615)
	return s1 + "|" + s2 + "|" + s3 + "|" + hex(b)
}
func appendFamily() string {
	a := binary.LittleEndian.AppendUint16(nil, 0x0102)
	a = binary.BigEndian.AppendUint32(a, 0x01020304)
	a = binary.NativeEndian.AppendUint64(a, 1)
	p := binary.BigEndian.AppendUint16([]byte("p:"), 0xffff)
	return hex(a) + "|" + strconv.Itoa(len(a)) + "|" + hex(p)
}
func orderStrings() string {
	return binary.LittleEndian.String() + "|" + binary.BigEndian.String() + "|" + binary.NativeEndian.String() + "|" + binary.LittleEndian.GoString() + "|" + binary.BigEndian.GoString()
}
func ifaceDispatch() string {
	orders := []binary.ByteOrder{binary.LittleEndian, binary.BigEndian, binary.NativeEndian}
	out := ""
	for _, o := range orders {
		b := make([]byte, 4)
		o.PutUint32(b, 0x01020304)
		out += o.String() + ":" + hex(b) + ":" + u(uint64(o.Uint16(b))) + ";"
	}
	var ab binary.AppendByteOrder = binary.BigEndian
	return out + hex(ab.AppendUint16(nil, 0x0102)) + ab.String()
}

func main() {
	allOrdersUint()
	putFamily()
	appendFamily()
	orderStrings()
	ifaceDispatch()
}
