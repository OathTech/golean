package main

// CL2 (window charter §4.2; docs/2026-10-03_window-corpus-disposition.md):
// the customer's `readOnly.recvAck` shape (raftsubject/raft/
// read_only.go:65) through the REAL encoding/binary. Nil and empty
// context are no-ops; >= 8 bytes decode little-endian (only the first
// 8 are read); a missing key reads as zero; the max update goes both
// ways; the input bytes and the unrelated entry are preserved; lengths
// 1..7 are the EXPLICIT panic case (encoding/binary's `_ = b[7]`); a
// nil acks map panics only when the context is non-empty. A miniature
// fixture is NOT a proof of Raft.

import "encoding/binary"

type readOnly struct {
	acks map[uint64]uint64
}

func (ro *readOnly) recvAck(from uint64, ctx []byte) {
	if len(ctx) != 0 {
		ro.acks[from] = max(ro.acks[from], binary.LittleEndian.Uint64(ctx))
	}
}

// ctxOf(n): n < 0 → nil; n == 0 → []byte{} (non-nil, empty);
// n > 0 → n bytes 1, 2, …, n.
func ctxOf(n int) []byte {
	if n < 0 {
		return nil
	}
	b := []byte{}
	for i := 0; i < n; i++ {
		b = append(b, byte(i+1))
	}
	return b
}

func sum(b []byte) int {
	s := 0
	for i, x := range b {
		s += (i + 1) * int(x)
	}
	return s
}

// recvAckLen(from, n): acks starts {1: 5, 9: 77}; from 1 exercises the
// max against an existing entry, from 2 the missing-key zero.
func recvAckLen(from, n int) (uint64, int, uint64, bool, int) {
	ro := &readOnly{acks: map[uint64]uint64{1: 5, 9: 77}}
	ctx := ctxOf(n)
	before := sum(ctx)
	ro.recvAck(uint64(from), ctx)
	_, present := ro.acks[uint64(from)]
	return ro.acks[uint64(from)], len(ro.acks), ro.acks[9], present, sum(ctx) - before
}

// The max keeps the larger: an existing entry above the decoded word.
func recvAckKeepsLarger() (uint64, uint64) {
	ro := &readOnly{acks: map[uint64]uint64{1: 1 << 60}}
	ctx := make([]byte, 8)
	binary.LittleEndian.PutUint64(ctx, 42)
	ro.recvAck(1, ctx)
	ro.recvAck(3, ctx)
	return ro.acks[1], ro.acks[3]
}

// A nil acks map: a read of a missing key is zero; the empty-context
// call is a no-op; the 8-byte call reads (zero), then the store panics.
func recvAckNilMap(n int) (uint64, int) {
	ro := &readOnly{}
	ro.recvAck(1, ctxOf(n))
	return ro.acks[1], len(ro.acks)
}

// The byte-to-word shifts by hand agree with encoding/binary on the
// first 8 bytes of a 9-byte context.
func handDecode() (uint64, uint64, bool) {
	b := ctxOf(9)
	b[7] = 0xfe
	var w uint64
	for i := 0; i < 8; i++ {
		w |= uint64(b[i]) << (8 * i)
	}
	lib := binary.LittleEndian.Uint64(b)
	return w, lib, w == lib
}

func main() {
	println(recvAckLen(1, 8))
	println(recvAckKeepsLarger())
	println(recvAckNilMap(0))
	println(handDecode())
}
