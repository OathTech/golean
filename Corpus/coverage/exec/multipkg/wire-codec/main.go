package main

// H-1 codec guardrails (raft W4.1 item 1): the language shapes the
// GENERATED plainpb codec runs on, pinned differentially — varint
// bit-ops over byte slices, single-byte tags in field-number order,
// proto2 pointer presence, merge-style decode with unknown-field
// skipping, and cross-package interface type-switch dispatch. The
// local package wirepb mirrors the generator's output forms exactly.

import "wirepb"

func u64(v uint64) *uint64 { return &v }

// codecRoundTrip is the stepLeader shape: ConfChange bytes produced by
// the encoder, carried in an Entry's Data, decoded by Unmarshal, fields
// read back.
func codecRoundTrip() int {
	t := int32(1)
	cc := &wirepb.ConfChange{Type: &t, NodeId: u64(300), Context: []byte("ab"), Id: u64(7)}
	ent := &wirepb.Entry{Term: u64(5), Data: wirepb.Marshal(cc)}
	out := &wirepb.ConfChange{}
	if !out.UnmarshalMessage(ent.Data) {
		return -1
	}
	sum := 0
	if out.Id != nil && *out.Id == 7 {
		sum += 1
	}
	if out.Type != nil && *out.Type == 1 {
		sum += 10
	}
	if out.NodeId != nil && *out.NodeId == 300 {
		sum += 100
	}
	if len(out.Context) == 2 && out.Context[0] == 'a' && out.Context[1] == 'b' {
		sum += 1000
	}
	return sum
}

// codecSize is the entsSize shape: Size over entries equals the length
// of the encoding, including varint width growth.
func codecSize() int {
	e1 := &wirepb.Entry{Term: u64(1), Index: u64(2), Data: []byte("x")}
	e2 := &wirepb.Entry{Term: u64(1 << 40), Index: u64(^uint64(0))}
	e3 := &wirepb.Entry{}
	sum := 0
	total := 0
	for _, e := range []*wirepb.Entry{e1, e2, e3} {
		s := wirepb.Size(e)
		b := wirepb.Marshal(e)
		if s == len(b) {
			sum++
		}
		total += s
	}
	return sum*1000 + total
}

// codecGolden pins exact hand-computed bytes: field-number order beats
// struct order, present-but-zero emits, 300 = 0xac 0x02.
func codecGolden() int {
	zero := int32(0)
	cc := &wirepb.ConfChange{Type: &zero, NodeId: u64(300)}
	b := wirepb.Marshal(cc)
	want := []byte{0x10, 0x00, 0x18, 0xac, 0x02}
	if len(b) != len(want) {
		return -1
	}
	for i := range b {
		if b[i] != want[i] {
			return i + 1
		}
	}
	return 0
}

// codecUnknownSkip: a decoder must skip unknown fields (varint and
// length-delimited) and still land the known ones after them.
func codecUnknownSkip() int {
	raw := []byte{
		0x78, 0x2a, // field 15, varint 42 — unknown, skipped
		0x7a, 0x02, 0xff, 0xff, // field 15, bytes len 2 — unknown, skipped
		0x18, 0x09, // NodeId = 9
	}
	out := &wirepb.ConfChange{}
	if !out.UnmarshalMessage(raw) {
		return -1
	}
	if out.NodeId == nil {
		return -2
	}
	return int(*out.NodeId)
}

// codecMalformed: truncated varints, truncated bytes bodies, field
// number zero, and 10-byte varint overflow all refuse (decode returns
// false), never a wrong answer.
func codecMalformed() int {
	sum := 0
	bad := [][]byte{
		{0x18},                   // truncated varint value
		{0x22, 0x05, 0x61},       // bytes body shorter than its length
		{0x00},                   // field number 0
		{0x18, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x02}, // varint overflow
	}
	for _, raw := range bad {
		out := &wirepb.ConfChange{}
		if !out.UnmarshalMessage(raw) {
			sum++
		}
	}
	return sum
}

func main() {
	println(codecRoundTrip(), codecSize(), codecGolden(), codecUnknownSkip(), codecMalformed())
}
