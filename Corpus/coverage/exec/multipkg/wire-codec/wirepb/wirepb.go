package wirepb

// A minimal protobuf-wire codec over two message shapes, mirroring the
// GENERATED plainpb codec's forms exactly (tools/raftsubject/derive.py
// gen_codec, raft W4.1 item 1): base-128 varints, single-byte tags in
// field-number order, proto2 pointer presence, merge-style unmarshal
// with unknown-field skipping, and interface type-switch dispatch from
// an importing package. These rows are the corpus pin for the LANGUAGE
// SHAPES the derived codec runs on — the derived codec itself is
// validated by tools/raftsubject/codeccheck.py (both oracles) and
// difftest.py section 7 (vs the real protobuf runtime).

type Entry struct {
	Term  *uint64
	Index *uint64
	Data  []byte
}

func (*Entry) ProtoMessage() {}

// ConfChange mirrors raftpb.ConfChange's numbering: Id=1, Type=2,
// NodeId=3, Context=4 — struct order differs from number order on
// purpose (so the field-number-ordered encoder is actually exercised).
type ConfChange struct {
	Type    *int32
	NodeId  *uint64
	Context []byte
	Id      *uint64
}

func (*ConfChange) ProtoMessage() {}

type Message interface{ ProtoMessage() }

func appendVarint(b []byte, v uint64) []byte {
	for v >= 0x80 {
		b = append(b, byte(v)|0x80)
		v >>= 7
	}
	return append(b, byte(v))
}

func sizeVarint(v uint64) int {
	n := 1
	for v >= 0x80 {
		v >>= 7
		n++
	}
	return n
}

func consumeVarint(b []byte, i int) (uint64, int, bool) {
	var v uint64
	for k := 0; k < 10; k++ {
		if i+k >= len(b) {
			return 0, 0, false
		}
		c := b[i+k]
		if k == 9 && c > 1 {
			return 0, 0, false
		}
		v |= uint64(c&0x7f) << (7 * k)
		if c < 0x80 {
			return v, i + k + 1, true
		}
	}
	return 0, 0, false
}

func skipField(b []byte, i int, wire uint64) (int, bool) {
	switch wire {
	case 0:
		_, j, ok := consumeVarint(b, i)
		if !ok {
			return 0, false
		}
		return j, true
	case 2:
		n, j, ok := consumeVarint(b, i)
		if !ok || uint64(len(b)-j) < n {
			return 0, false
		}
		return j + int(n), true
	}
	return 0, false
}

// Entry: Term=2, Index=3, Data=4 (raftpb numbering; Type omitted here).

func (x *Entry) SizeMessage() int {
	if x == nil {
		return 0
	}
	n := 0
	if x.Term != nil {
		n += 1 + sizeVarint(*x.Term)
	}
	if x.Index != nil {
		n += 1 + sizeVarint(*x.Index)
	}
	if x.Data != nil {
		n += 1 + sizeVarint(uint64(len(x.Data))) + len(x.Data)
	}
	return n
}

func (x *Entry) AppendMessage(b []byte) []byte {
	if x == nil {
		return b
	}
	if x.Term != nil {
		b = append(b, 0x10)
		b = appendVarint(b, *x.Term)
	}
	if x.Index != nil {
		b = append(b, 0x18)
		b = appendVarint(b, *x.Index)
	}
	if x.Data != nil {
		b = append(b, 0x22)
		b = appendVarint(b, uint64(len(x.Data)))
		b = append(b, x.Data...)
	}
	return b
}

func (x *ConfChange) SizeMessage() int {
	if x == nil {
		return 0
	}
	n := 0
	if x.Id != nil {
		n += 1 + sizeVarint(*x.Id)
	}
	if x.Type != nil {
		n += 1 + sizeVarint(uint64(*x.Type))
	}
	if x.NodeId != nil {
		n += 1 + sizeVarint(*x.NodeId)
	}
	if x.Context != nil {
		n += 1 + sizeVarint(uint64(len(x.Context))) + len(x.Context)
	}
	return n
}

func (x *ConfChange) AppendMessage(b []byte) []byte {
	if x == nil {
		return b
	}
	if x.Id != nil {
		b = append(b, 0x08)
		b = appendVarint(b, *x.Id)
	}
	if x.Type != nil {
		b = append(b, 0x10)
		b = appendVarint(b, uint64(*x.Type))
	}
	if x.NodeId != nil {
		b = append(b, 0x18)
		b = appendVarint(b, *x.NodeId)
	}
	if x.Context != nil {
		b = append(b, 0x22)
		b = appendVarint(b, uint64(len(x.Context)))
		b = append(b, x.Context...)
	}
	return b
}

func (x *ConfChange) UnmarshalMessage(b []byte) bool {
	i := 0
	for i < len(b) {
		tag, j, ok := consumeVarint(b, i)
		if !ok {
			return false
		}
		i = j
		num := tag >> 3
		wire := tag & 7
		if num == 0 {
			return false
		}
		switch {
		case num == 1 && wire == 0:
			v, j2, ok2 := consumeVarint(b, i)
			if !ok2 {
				return false
			}
			x.Id = &v
			i = j2
		case num == 2 && wire == 0:
			v, j2, ok2 := consumeVarint(b, i)
			if !ok2 {
				return false
			}
			ev := int32(uint32(v))
			x.Type = &ev
			i = j2
		case num == 3 && wire == 0:
			v, j2, ok2 := consumeVarint(b, i)
			if !ok2 {
				return false
			}
			x.NodeId = &v
			i = j2
		case num == 4 && wire == 2:
			n, j2, ok2 := consumeVarint(b, i)
			if !ok2 || uint64(len(b)-j2) < n {
				return false
			}
			s := make([]byte, n)
			copy(s, b[j2:j2+int(n)])
			x.Context = s
			i = j2 + int(n)
		default:
			j2, ok2 := skipField(b, i, wire)
			if !ok2 {
				return false
			}
			i = j2
		}
	}
	return true
}

// Marshal / Size dispatch through the Message interface — the same
// cross-package type-switch shape as the subject-local proto package.
func Marshal(m Message) []byte {
	switch x := m.(type) {
	case *Entry:
		return x.AppendMessage(nil)
	case *ConfChange:
		return x.AppendMessage(nil)
	}
	panic("wirepb: message type outside the modeled set")
}

func Size(m Message) int {
	switch x := m.(type) {
	case *Entry:
		return x.SizeMessage()
	case *ConfChange:
		return x.SizeMessage()
	}
	panic("wirepb: message type outside the modeled set")
}
