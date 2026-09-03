package main

// encoding/binary through the REAL source-through package (slice 2,
// 2026-09-03): the LittleEndian.{Uint64,PutUint64} package-variable
// method desugar RETIRED — `binary.LittleEndian` is the library's own
// package-level variable of the unexported type littleEndian, whose full
// method set lowers (Uint16/32/64, PutUint16/32/64, AppendUint*, String,
// GoString); BigEndian likewise; the ByteOrder INTERFACE dispatches onto
// them. Read/Write/Size (reflect) refuse by name — not rowed here.

import "encoding/binary"

func leRoundTrip64() (uint64, string) {
	b := make([]byte, 8)
	binary.LittleEndian.PutUint64(b, 0x0102030405060708)
	hex := ""
	for _, c := range b {
		hex += string("0123456789abcdef"[c>>4]) + string("0123456789abcdef"[c&0xf])
	}
	return binary.LittleEndian.Uint64(b), hex
}

func beRoundTrip() (uint32, uint16, string) {
	b := make([]byte, 6)
	binary.BigEndian.PutUint32(b, 0xdeadbeef)
	binary.BigEndian.PutUint16(b[4:], 0xcafe)
	hex := ""
	for _, c := range b {
		hex += string("0123456789abcdef"[c>>4]) + string("0123456789abcdef"[c&0xf])
	}
	return binary.BigEndian.Uint32(b), binary.BigEndian.Uint16(b[4:]), hex
}

func appendOrders() (int, string) {
	b := binary.LittleEndian.AppendUint16(nil, 0x0102)
	b = binary.BigEndian.AppendUint32(b, 0x03040506)
	b = binary.LittleEndian.AppendUint64(b, 0x0708090a0b0c0d0e)
	hex := ""
	for _, c := range b {
		hex += string("0123456789abcdef"[c>>4]) + string("0123456789abcdef"[c&0xf])
	}
	return len(b), hex
}

func byteOrderInterface() (uint16, uint16, string, string) {
	var lo, bo binary.ByteOrder = binary.LittleEndian, binary.BigEndian
	b := []byte{0x12, 0x34}
	return lo.Uint16(b), bo.Uint16(b), lo.String(), bo.String()
}

func putShortPanics() uint32 {
	b := make([]byte, 3)
	binary.BigEndian.PutUint32(b, 1)
	return binary.BigEndian.Uint32(b)
}

func main() {
	v, h := leRoundTrip64()
	println(v, h)
	a, c, h2 := beRoundTrip()
	println(a, c, h2)
	n, h3 := appendOrders()
	println(n, h3)
	x, y, s1, s2 := byteOrderInterface()
	println(x, y, s1, s2)
}
