package main

// binary.LittleEndian.{Uint64,PutUint64} conformance pins (raft W4.1
// item 4 — H-14/G-8, read_only.go's recvAck/heartbeatCtx shapes). The
// call is a METHOD on the package VARIABLE binary.LittleEndian (an
// unexported type), so it rides the desugar hook rather than the plain
// E5 selector-call path; the shims mirror encoding/binary's bodies,
// including the leading `_ = b[7]` bounds check whose out-of-range
// panic is the failure mode pinned below.

import "encoding/binary"

func leRoundTrip() uint64 {
	b := make([]byte, 8)
	binary.LittleEndian.PutUint64(b, 0x0123456789abcdef)
	return binary.LittleEndian.Uint64(b)
}

// Golden bytes: little-endian means least significant byte first.
func leGolden() int {
	b := make([]byte, 8)
	binary.LittleEndian.PutUint64(b, 0x0123456789abcdef)
	want := []byte{0xef, 0xcd, 0xab, 0x89, 0x67, 0x45, 0x23, 0x01}
	for i := range b {
		if b[i] != want[i] {
			return i + 1
		}
	}
	return 0
}

// The heartbeatCtx shape (read_only.go): context bytes carry an index.
func leHeartbeatCtxShape() uint64 {
	ctx := make([]byte, 8)
	binary.LittleEndian.PutUint64(ctx, 42)
	acked := binary.LittleEndian.Uint64(ctx)
	if acked > 40 {
		return acked
	}
	return 0
}

// Reading past the end panics with gc's bounds message (the `_ = b[7]`
// check in encoding/binary's own body).
func leShortRead() uint64 {
	short := []byte{1, 2, 3}
	return binary.LittleEndian.Uint64(short)
}

func main() {
	println(leRoundTrip(), leGolden(), leHeartbeatCtxShape())
}
