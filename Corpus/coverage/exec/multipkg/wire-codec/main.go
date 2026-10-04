package main

// H-1 codec guardrails (raft W4.1 item 1), RE-BORN for protobuf route A
// slice S1 (docs/2026-10-04_route-a-protobuf-design.md D9, acceptance §5;
// [USER] Mike 2026-10-04 «Approved», relayed): the language shapes the
// GENERATED raftsubject codec runs on, pinned differentially (go run vs the
// machine). The local packages wirepb and wireproto are NOT hand-written:
// they are tools/raftsubject/derive.py's own codec generator run over a
// four-message synthetic schema (derive.py --check keeps them in sync), so
// every shape below is a shape the subject's codec contains — interface
// dispatch from an importing package, typed-nil arms, unknown-field
// retention, the group skipper with its depth counter, the message depth
// counter, the *prefixError value with its Unwrap sentinel, and the ONE
// init-time spelling pick (rand.Intn(2) on the intn pick site).
//
// Exactness against protobuf-go itself is NOT this file's job (protobuf-go
// is never a corpus oracle — fixtures are stdlib-only): that is
// tools/raftsubject/difftest.py section 8 (exact) and codeccheck.py (both
// oracles over the subject codec). Every strict row here returns a value
// that does not depend on the init pick; the two membership rows are the
// ones whose observable IS the pick.
//
// NOT here: the recursion edges (10000 vs 10001 nested messages; 10001 vs
// 10002 nested groups). Each edge decode needs 10M-40M machine steps, past
// the strict lane's fixed 10M fuel, so a row would be red by budget, not by
// semantics — measured 2026-10-04 and reported as an open item of route A
// S1; the edges are checked by codeccheck.py (the machine leg, raised fuel)
// and difftest.py section 8 (exact vs protobuf-go).

import (
	"wirepb"
	"wireproto"
)

func u64(v uint64) *uint64 { return &v }

// digest folds a byte slice into one int (nil -> -1, so nil and empty
// differ): the row's observable for a re-encoding.
func digest(b []byte) int {
	if b == nil {
		return -1
	}
	h := len(b)
	for i := 0; i < len(b); i++ {
		h = (h*31 + int(b[i])) % 1000003
	}
	return h
}

// isDecodeErr: err is the codec's errDecode — one of its two spellings.
func isDecodeErr(err error) bool {
	if err == nil {
		return false
	}
	s := err.Error()
	if s == "proto: cannot parse invalid wire-format data" {
		return true
	}
	return s == "proto:\u00a0cannot parse invalid wire-format data"
}

func isDepthErr(err error) bool {
	if err == nil {
		return false
	}
	s := err.Error()
	if s == "proto: exceeded maximum recursion depth" {
		return true
	}
	return s == "proto:\u00a0exceeded maximum recursion depth"
}

// decodeCC decodes raw into a fresh ConfChange and returns (re-encoding
// digest, Size, error verdict 0/1).
func decodeCC(raw []byte) (int, int, int) {
	out := &wirepb.ConfChange{}
	err := wireproto.Unmarshal(raw, out)
	bad := 0
	if err != nil {
		bad = 1
	}
	b, _ := wireproto.Marshal(out)
	return digest(b), wireproto.Size(out), bad
}

// ---- the pre-route-A rows (observations unchanged) ----------------------

// codecRoundTrip is the stepLeader shape: ConfChange bytes produced by
// the encoder, carried in an Entry's Data, decoded by Unmarshal, fields
// read back.
func codecRoundTrip() int {
	t := wirepb.ConfChangeType(1)
	cc := &wirepb.ConfChange{Type: &t, NodeId: u64(300), Context: []byte("ab"), Id: u64(7)}
	data, _ := wireproto.Marshal(cc)
	ent := &wirepb.Entry{Term: u64(5), Data: data}
	out := &wirepb.ConfChange{}
	if wireproto.Unmarshal(ent.Data, out) != nil {
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
	es := []*wirepb.Entry{e1, e2, e3}
	sum := 0
	total := 0
	for i := 0; i < len(es); i++ {
		s := wireproto.Size(es[i])
		b, _ := wireproto.Marshal(es[i])
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
	zero := wirepb.ConfChangeType(0)
	cc := &wirepb.ConfChange{Type: &zero, NodeId: u64(300)}
	b, _ := wireproto.Marshal(cc)
	want := []byte{0x10, 0x00, 0x18, 0xac, 0x02}
	if len(b) != len(want) {
		return -1
	}
	for i := 0; i < len(b); i++ {
		if b[i] != want[i] {
			return i + 1
		}
	}
	return 0
}

// codecUnknownSkip: a decoder must get past unknown fields (varint and
// length-delimited) and still land the known ones after them.
func codecUnknownSkip() int {
	raw := []byte{
		0x78, 0x2a, // field 15, varint 42 — unknown
		0x7a, 0x02, 0xff, 0xff, // field 15, bytes len 2 — unknown
		0x18, 0x09, // NodeId = 9
	}
	out := &wirepb.ConfChange{}
	if wireproto.Unmarshal(raw, out) != nil {
		return -1
	}
	if out.NodeId == nil {
		return -2
	}
	return int(*out.NodeId)
}

// codecMalformed: truncated varints, truncated bytes bodies, field
// number zero, and 10-byte varint overflow all refuse (an error), never a
// wrong answer.
func codecMalformed() int {
	sum := 0
	bad := [][]byte{
		{0x18},             // truncated varint value
		{0x22, 0x05, 0x61}, // bytes body shorter than its length
		{0x00},             // field number 0
		{0x18, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x02}, // varint overflow
	}
	for i := 0; i < len(bad); i++ {
		out := &wirepb.ConfChange{}
		if wireproto.Unmarshal(bad[i], out) != nil {
			sum++
		}
	}
	return sum
}

// ---- route A rows (S1) ---------------------------------------------------

// unknown-retain-reencode: unknown fields are RETAINED — the tag
// canonicalized (a 3-byte tag for field 15 re-encodes as 0x78), arrival
// order kept — and re-emitted AFTER the known fields; Size counts them.
func codecUnknownRetainReencode() int {
	raw := []byte{
		0xf8, 0x80, 0x00, 0x2a, // field 15 varint 42, non-minimal 3-byte tag
		0x18, 0x09, // NodeId = 9 (known)
		0x82, 0x01, 0x02, 0xff, 0xfe, // field 16, bytes {ff fe}
	}
	d, sz, bad := decodeCC(raw)
	b, _ := wireproto.Marshal(&wirepb.ConfChange{NodeId: u64(9)})
	want := []byte{0x18, 0x09, 0x78, 0x2a, 0x82, 0x01, 0x02, 0xff, 0xfe}
	ok := 0
	if d == digest(want) && sz == len(want) && digest(b) == digest(want[:2]) {
		ok = 1
	}
	return ok*1000000 + bad*100000 + d%100000
}

// wrong-wiretype-retain: a KNOWN field (Type, 2) at a wrong wire type is an
// unknown field, retained; the known field stays unset.
func codecWrongWiretypeRetain() int {
	raw := []byte{0x12, 0x01, 0x00} // field 2 with wire type 2
	out := &wirepb.ConfChange{}
	err := wireproto.Unmarshal(raw, out)
	b, _ := wireproto.Marshal(out)
	r := digest(b)
	if err != nil {
		r += 1000000
	}
	if out.Type != nil {
		r += 2000000
	}
	return r
}

// group-skip-nested: an unknown GROUP is skipped and retained whole, at
// nesting depths 0..3, each holding one unknown field.
func codecGroupSkipNested() int {
	cases := [][]byte{
		{0x7b, 0x7c}, // depth 0: empty group 15
		{0x7b, 0x08, 0x01, 0x7c},
		{0x7b, 0x83, 0x01, 0x08, 0x01, 0x84, 0x01, 0x7c},
		{0x7b, 0x83, 0x01, 0x8b, 0x01, 0x08, 0x01, 0x8c, 0x01, 0x84, 0x01, 0x7c},
	}
	r := 0
	for i := 0; i < len(cases); i++ {
		raw := append([]byte{0x18, 0x05}, cases[i]...)
		d, sz, bad := decodeCC(raw)
		ok := 0
		if bad == 0 && d == digest(raw) && sz == len(raw) {
			ok = 1
		}
		r = r*10 + ok
	}
	return r
}

// group-end-mismatch, group-truncated, stray-end-group, field-number-zero:
// each is errDecode (one of its two spellings).
func codecGroupEndMismatch() int {
	_, _, bad := decodeCC([]byte{0x7b, 0x84, 0x01})
	out := &wirepb.ConfChange{}
	err := wireproto.Unmarshal([]byte{0x7b, 0x84, 0x01}, out)
	if isDecodeErr(err) {
		return bad + 10
	}
	return bad
}

func codecGroupTruncated() int {
	r := 0
	ins := [][]byte{{0x7b}, {0x7b, 0x08}, {0x7b, 0x08, 0x01}}
	for i := 0; i < len(ins); i++ {
		err := wireproto.Unmarshal(ins[i], &wirepb.ConfChange{})
		if isDecodeErr(err) {
			r++
		}
	}
	return r
}

func codecStrayEndGroup() int {
	r := 0
	ins := [][]byte{{0x7c}, {0x0c}, {0x18, 0x01, 0x7c}}
	for i := 0; i < len(ins); i++ {
		err := wireproto.Unmarshal(ins[i], &wirepb.ConfChange{})
		if isDecodeErr(err) {
			r++
		}
	}
	return r
}

func codecFieldNumberZero() int {
	r := 0
	ins := [][]byte{{0x00, 0x01}, {0x02, 0x00}, {0x80, 0x00, 0x01}}
	for i := 0; i < len(ins); i++ {
		err := wireproto.Unmarshal(ins[i], &wirepb.ConfChange{})
		if isDecodeErr(err) {
			r++
		}
	}
	return r
}

// field-number-max: 2^29-1 is the largest valid number — accepted and
// retained.
func codecFieldNumberMax() int {
	raw := []byte{0xf8, 0xff, 0xff, 0xff, 0x0f, 0x01}
	d, sz, bad := decodeCC(raw)
	return bad*1000000 + sz*10000 + d%10000
}

// field-number-over-max-top-vs-in-group: 2^29 is REFUSED at the message
// level (impl/decode.go:149-155) but ACCEPTED inside a skipped group, where
// only number < 1 is refused (protowire ConsumeTag).
func codecFieldNumberOverMax() int {
	top := []byte{0x80, 0x80, 0x80, 0x80, 0x10, 0x01}
	grp := []byte{0x7b, 0x80, 0x80, 0x80, 0x80, 0x10, 0x01, 0x7c}
	_, _, badTop := decodeCC(top)
	d, sz, badGrp := decodeCC(grp)
	return badTop*1000000 + badGrp*100000 + sz*1000 + d%1000
}

// varint-ten-bytes: the longest valid varint (2^64-1) is accepted.
func codecVarintTenBytes() int {
	raw := []byte{0x08, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x01}
	out := &wirepb.ConfChange{}
	if wireproto.Unmarshal(raw, out) != nil {
		return -1
	}
	if out.Id == nil || *out.Id != ^uint64(0) {
		return -2
	}
	return wireproto.Size(out)
}

// varint-overflow (a 10th byte >= 2) and varint-truncated: errDecode.
func codecVarintOverflow() int {
	r := 0
	ins := [][]byte{
		{0x08, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x02},
		{0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x01},
		{0x78, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x7f},
	}
	for i := 0; i < len(ins); i++ {
		if isDecodeErr(wireproto.Unmarshal(ins[i], &wirepb.ConfChange{})) {
			r++
		}
	}
	return r
}

func codecVarintTruncated() int {
	r := 0
	ins := [][]byte{{0x08, 0xff, 0xff}, {0x80}, {0x78}, {0x78, 0x80}}
	for i := 0; i < len(ins); i++ {
		if isDecodeErr(wireproto.Unmarshal(ins[i], &wirepb.ConfChange{})) {
			r++
		}
	}
	return r
}

// packed-accepted-unpacked-emitted: a PACKED repeated varint field is
// accepted (and may interleave with unpacked elements); the encoder emits
// it UNPACKED.
func codecPackedAcceptedUnpackedEmitted() int {
	raw := []byte{0x0a, 0x03, 0x01, 0xac, 0x02, 0x08, 0x05} // packed {1,300} + unpacked 5
	out := &wirepb.ConfState{}
	if wireproto.Unmarshal(raw, out) != nil {
		return -1
	}
	b, _ := wireproto.Marshal(out)
	want := []byte{0x08, 0x01, 0x08, 0xac, 0x02, 0x08, 0x05}
	r := len(out.Voters) * 1000
	if digest(b) == digest(want) {
		r++
	}
	return r
}

// bytes-empty-presence: an empty-but-present bytes field decodes to a
// NON-nil empty slice and re-encodes (0x22 0x00); an absent one stays nil.
func codecBytesEmptyPresence() int {
	out := &wirepb.ConfChange{}
	if wireproto.Unmarshal([]byte{0x22, 0x00}, out) != nil {
		return -1
	}
	r := 0
	if out.Context != nil {
		r += 1
	}
	b, _ := wireproto.Marshal(out)
	if len(b) == 2 {
		r += 10
	}
	abs := &wirepb.ConfChange{}
	if wireproto.Unmarshal([]byte{0x18, 0x01}, abs) != nil {
		return -2
	}
	if abs.Context == nil {
		r += 100
	}
	return r
}

// merge-twice-singular: a singular embedded message occurring twice
// MERGES (repeated fields append, scalars last-wins).
func codecMergeTwiceSingular() int {
	raw := []byte{
		0x4a, 0x02, 0x08, 0x01, // Conf {Voters: [1]}
		0x4a, 0x04, 0x08, 0x02, 0x28, 0x01, // Conf {Voters: [2], AutoLeave: true}
	}
	out := &wirepb.Message{}
	if wireproto.Unmarshal(raw, out) != nil {
		return -1
	}
	if out.Conf == nil {
		return -2
	}
	r := len(out.Conf.Voters) * 100
	if out.Conf.AutoLeave != nil && *out.Conf.AutoLeave {
		r += 1
	}
	return r
}

// enum-unlisted-value-stored: proto2 enums are OPEN in protobuf-go
// (coderEnumPtr = coderInt32Ptr): an unlisted value is stored, int32-
// truncated, never diverted to the unknown fields.
func codecEnumUnlistedValueStored() int {
	out := &wirepb.ConfChange{}
	if wireproto.Unmarshal([]byte{0x10, 0x63}, out) != nil {
		return -1
	}
	if out.Type == nil {
		return -2
	}
	neg := &wirepb.ConfChange{}
	raw := []byte{0x10, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x01}
	if wireproto.Unmarshal(raw, neg) != nil {
		return -3
	}
	return int(*out.Type)*1000 + int(*neg.Type) + wireproto.Size(neg)*100000
}

// typed-nil-marshal: Marshal of a TYPED-NIL message answers nil (not the
// empty non-nil buffer a valid empty message gets) and no error.
func codecTypedNilMarshal() int {
	var tn *wirepb.Entry
	b, err := wireproto.Marshal(tn)
	r := 0
	if b == nil {
		r += 1
	}
	if err == nil {
		r += 10
	}
	e, _ := wireproto.Marshal(&wirepb.Entry{})
	if e != nil && len(e) == 0 {
		r += 100
	}
	n, _ := wireproto.Marshal(nil)
	if n == nil {
		r += 1000
	}
	return r
}

// typed-nil-size: Size of a typed nil (and of a nil interface) is 0.
func codecTypedNilSize() int {
	var tn *wirepb.Message
	return wireproto.Size(tn)*10 + wireproto.Size(nil) + 7
}

// typed-nil-clone: Clone of a typed nil is the typed nil (a NON-nil
// interface holding a nil pointer); Clone of a nil interface is nil.
func codecTypedNilClone() int {
	var tn *wirepb.ConfState
	c := wireproto.Clone(tn)
	r := 0
	if c != nil {
		r += 1
	}
	p, ok := c.(*wirepb.ConfState)
	if ok && p == nil {
		r += 10
	}
	if wireproto.Clone(nil) == nil {
		r += 100
	}
	return r
}

// typed-nil-equal: two typed nils of one type are equal; a typed nil is
// not equal to a valid empty message, nor to a nil interface.
func codecTypedNilEqual() int {
	var a *wirepb.Entry
	var b *wirepb.Entry
	r := 0
	if wireproto.Equal(a, b) {
		r += 1
	}
	if !wireproto.Equal(a, &wirepb.Entry{}) {
		r += 10
	}
	if !wireproto.Equal(nil, a) {
		r += 100
	}
	if wireproto.Equal(nil, nil) {
		r += 1000
	}
	return r
}

// nil-and-empty-input: nil and empty data both decode to an empty message;
// an empty message re-encodes to a zero-length NON-nil buffer.
func codecNilAndEmptyInput() int {
	r := 0
	a := &wirepb.ConfChange{Id: u64(3)}
	if wireproto.Unmarshal(nil, a) == nil && a.Id == nil {
		r += 1
	}
	b := &wirepb.ConfChange{Id: u64(3)}
	if wireproto.Unmarshal([]byte{}, b) == nil && b.Id == nil {
		r += 10
	}
	m, _ := wireproto.Marshal(a)
	if m != nil && len(m) == 0 {
		r += 100
	}
	return r
}

// sentinel-unwrap: the decode error unwraps to the package sentinel
// wireproto.Error (errors.Is itself is refused on the machine, FR-14).
func codecSentinelUnwrap() int {
	err := wireproto.Unmarshal([]byte{0x00}, &wirepb.Entry{})
	if err == nil {
		return -1
	}
	u, ok := err.(interface{ Unwrap() error })
	if !ok {
		return -2
	}
	if u.Unwrap() != wireproto.Error {
		return -3
	}
	return len(wireproto.Error.Error())
}

// prefix-pick (MEMBERSHIP): the error text's length is the init pick —
// 44 ("proto: " + 37) or 45 ("proto:" + U+00A0, two bytes, + 37).
func codecPrefixPick() int {
	err := wireproto.Unmarshal([]byte{0x00}, &wirepb.Entry{})
	if err == nil {
		return -1
	}
	return len(err.Error())
}

// panic-abort-text (MEMBERSHIP): raft's stepLeader shape — panic(err) with
// the decode error VALUE — aborts with the error's text, either spelling.
func codecPanicAbortText() int {
	cc := &wirepb.ConfChange{}
	if err := wireproto.Unmarshal([]byte{0x7b}, cc); err != nil {
		panic(err)
	}
	return 0
}

func main() {
	println(codecRoundTrip(), codecSize(), codecGolden(), codecUnknownSkip(), codecMalformed())
	println(codecUnknownRetainReencode(), codecWrongWiretypeRetain(), codecGroupSkipNested(), codecGroupEndMismatch(), codecGroupTruncated(), codecStrayEndGroup())
	println(codecFieldNumberZero(), codecFieldNumberMax(), codecFieldNumberOverMax(), codecVarintTenBytes(), codecVarintOverflow(), codecVarintTruncated())
	println(codecPackedAcceptedUnpackedEmitted(), codecBytesEmptyPresence(), codecMergeTwiceSingular(), codecEnumUnlistedValueStored())
	println(codecTypedNilMarshal(), codecTypedNilSize(), codecTypedNilClone(), codecTypedNilEqual(), codecNilAndEmptyInput(), codecSentinelUnwrap())
	println(codecPrefixPick())
	codecPanicAbortText()
}
