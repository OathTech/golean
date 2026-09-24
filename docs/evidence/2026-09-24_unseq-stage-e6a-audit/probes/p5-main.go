package main

// Audit probes — Stage E6a attack 3/6: the twin's born-graph shapes and the status-diverse row.

func wit(x int) int { println("wit", x); return x }

type HS struct{ Term, Vote, Commit uint64 }

// protobuf-style getters: POINTER receivers, nil-checked bodies (the twin's raftpb spelling)
func (x *HS) GetTerm() uint64 {
	if x != nil {
		return x.Term
	}
	return 0
}
func (x *HS) GetVote() uint64 {
	if x != nil {
		return x.Vote
	}
	return 0
}
func (x *HS) GetCommit() uint64 {
	if x != nil {
		return x.Commit
	}
	return 0
}

func isHSEqual(a, b *HS) bool {
	return a.GetTerm() == b.GetTerm() && a.GetVote() == b.GetVote() && a.GetCommit() == b.GetCommit()
}

func hsEqualNonNil() int {
	a := &HS{1, 2, 3}
	b := &HS{1, 2, 4}
	if isHSEqual(a, b) {
		return 1
	}
	return 0
}

func hsEqualNilRight() int {
	a := &HS{0, 0, 0}
	if isHSEqual(a, nil) {
		return 1
	}
	return 0
}

// VALUE-receiver getters with a print: the auto-deref of a nil pointer operand vs the sibling call's print
type VS struct{ Term, Vote uint64 }

func (x VS) GetTerm() uint64 { println("get"); return x.Term }
func (x VS) GetVote() uint64 { println("getv"); return x.Vote }

func vsEqual(a, b *VS) bool { return a.GetTerm() == b.GetTerm() && a.GetVote() == b.GetVote() }

func vsEqualNilRight() int {
	a := &VS{1, 2}
	if vsEqual(a, nil) {
		return 1
	}
	return 0
}

func mustSyncShape(st, prevst *HS, n int) bool {
	return n != 0 || st.GetVote() != prevst.GetVote() || st.GetTerm() != prevst.GetTerm()
}

func mustSync() int {
	if mustSyncShape(&HS{1, 2, 3}, &HS{1, 2, 3}, 0) {
		return 1
	}
	return 0
}

type Snap struct {
	Data []byte
	Meta *HS
}

func (m *HS) Size() int { return 3 }

// SizeMessage's shape: a compound whose nil-checked field read is unordered against the sibling method call
func (m *Snap) SizeMessage() int {
	n := 0
	n += len(m.Data) + m.Meta.Size()
	return n
}

func sizeMessage() int {
	s := &Snap{Data: []byte{1, 2}, Meta: &HS{}}
	return s.SizeMessage()
}

func sizeMessageNilMeta() int {
	s := &Snap{Data: []byte{1, 2}}
	return s.SizeMessage()
}

// the status-diverse row's body
func strIndexStatusDiverse() int {
	s := "ab"
	i := 0
	m := func() int { i = 9; return 5 }
	return int(s[i]) + m()
}

func main() {}
